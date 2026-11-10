#!/usr/bin/env python3
"""Check the behavioral inventory, imports and embedded SQL source bindings.

This is an inventory/structure check, not an Agda check or a Rust refinement
proof. Run Agda separately and retain its complete log and process exit status.
"""
from pathlib import Path
import json
import re

ROOT = Path(__file__).resolve().parents[2]


def read(path):
    return (ROOT / path).read_text()


def enum_variants(path, name):
    match = re.search(r'(?:pub(?:\([^)]*\))? )?enum ' + name + r' \{(.*?)\n\}', read(path), re.S)
    assert match, (path, name)
    return re.findall(r'^    ([A-Z][A-Za-z]+)\b', match.group(1), re.M)


def kebab(name):
    return re.sub(r'(?<!^)(?=[A-Z])', '-', name).lower()


def embedded_sql_body(source):
    """Read our single-migration files without removing SQL body comments.

    The loader ends metadata at its terminating semicolon, not at the first
    non-comment line. Refuse unsupported headers rather than guessing where
    SQL begins. This checker supports the maintained JSON-valued header form.
    """
    lines = source.splitlines(keepends=True)
    if not lines or lines[0].strip() != '-- #!migration':
        raise ValueError('Expected a migration header')
    fields = {}
    for index, line in enumerate(lines[1:], 1):
        match = re.fullmatch(r'\s*--\s*(name|description|requires):\s*(.+)\s*([,;])\s*', line)
        if not match:
            raise ValueError('Unsupported or unterminated migration header')
        key, raw, separator = match.groups()
        value = json.loads(raw)
        if key in fields:
            raise ValueError('Repeated migration metadata field')
        if not isinstance(value, str) and not (
                key == 'requires' and isinstance(value, list)
                and all(isinstance(item, str) for item in value)):
            raise ValueError('Invalid migration metadata value')
        fields[key] = value
        if separator == ';':
            if not {'name', 'description'} <= fields.keys():
                raise ValueError('Missing migration name or description')
            body = ''.join(lines[index + 1:])
            if body.startswith('-- #!') or '\n-- #!' in body:
                raise ValueError('Expected one migration per embedded file')
            return body.strip()
    raise ValueError('Unterminated migration header')


def native_public_operations(source):
    """Read every declaration in the maintained closed public macro."""
    sites = dict(re.findall(r'Self::(\w+)\s*=>\s*"(store\.[^"]+)"', source))
    macro = source.split('operations! {', 1)[1].split('\n}\n', 1)[0]
    groups = re.findall(r'^    (\w+) \{(.*?)^    \}', macro, re.M | re.S)
    assert {name for name, _ in groups} == {'graph', 'learning', 'control'}, 'unsupported public operation group'
    assert len(groups) == len({name for name, _ in groups}), 'repeated public operation group'
    remainder = re.sub(r'^    \w+ \{.*?^    \}', '', macro, flags=re.M | re.S)
    assert not remainder.strip(), 'unparsed public operation declaration'
    operations = {}
    for group, body in groups:
        for line in body.splitlines():
            if not line.strip():
                continue
            entry = re.fullmatch(r'\s*\w+\s*=>\s*"([a-z_]+)"\s*\[([^\n]*)\],?\s*', line)
            assert entry, ('unsupported public operation declaration', line)
            name, boundary_body = entry.groups()
            assert name not in operations, ('repeated public operation', name)
            operations[name] = (group, native_boundaries(boundary_body, sites))
    assert operations, 'missing public operation declarations'
    return operations


def native_boundaries(body, sites):
    calls = re.findall(r'(once|repeated)\((\w+)\)', body)
    remainder = re.sub(r'(once|repeated)\(\w+\)', '', body)
    assert not remainder.strip(' ,\t\r\n'), ('unsupported boundary declaration', body)
    assert all(site in sites for _, site in calls), ('unknown commit site', body)
    return [(sites[site], mode == 'repeated') for mode, site in calls]


def native_registered_operations(source):
    """Business plans exclude controls, which own separate certificates."""
    sites = dict(re.findall(r'Self::(\w+)\s*=>\s*"(store\.[^"]+)"', source))
    operations = {name: boundaries for name, (group, boundaries)
                  in native_public_operations(source).items() if group != 'control'}
    private = source.split('impl RegisteredOperation {', 1)[1]
    names = dict(re.findall(r'Self::(\w+)\s*=>\s*"([a-z_]+)"', private))
    named = private.split('pub fn named', 1)[1].split('pub fn name(', 1)[0]
    assert '!matches!(operation, Operation::Control(_))' in named, 'controls must not enter business saved plans'
    assert set(re.findall(r'"([a-z_]+)"', named)) == set(names.values()), 'unmodelled named internal operation'
    for variant, name in names.items():
        match = re.search(r'Self::' + variant + r'\s*=>\s*\{\s*const PLAN:[^=]+=\s*&\[([^\]]*)\]', private)
        assert match, ('unsupported internal boundary declaration', variant)
        assert name not in operations, ('duplicate registered operation', name)
        operations[name] = native_boundaries(match.group(1), sites)
    return operations


def formal_public_operations(source):
    body = source.split('data Tool : Set where', 1)[1].split('data Kind', 1)[0]
    constructors = []
    for line in body.splitlines():
        line = line.split('--', 1)[0].strip()
        if not line:
            continue
        declaration = re.fullmatch(r'([A-Za-z ]+) : Tool', line)
        assert declaration, ('unsupported closed tool constructor', line)
        constructors.extend(declaration.group(1).split())
    names = re.findall(r'^wireName\s+(\w+)\s*=\s*"([a-z_]+)"$', source, re.M)
    kinds = re.findall(r'^kind\s+(\w+)\s*=\s*(businessWrite|readOnly|operationControl)$', source, re.M)
    assert len(constructors) == len(set(constructors)), 'repeated closed tool constructor'
    assert len(names) == len(dict(names)) == len({name for _, name in names}), 'repeated wire name'
    assert len(kinds) == len(dict(kinds)), 'repeated tool kind'
    assert set(constructors) == set(dict(names)) == set(dict(kinds)), 'closed tools, wire names and kinds disagree'
    return {name: dict(kinds)[constructor] for constructor, name in names}


def concrete_control_certificates(source):
    # These clauses assemble the actual reservation/readback/cancellation
    # certificates. Merely listing a control name is not coverage.
    body = source.split('module Controls ', 1)[1]
    assert re.search(r'operation : .*Recovery\.RecoverableFor Store\.World', body), 'control dispatch lacks required recovery certificate'
    clauses = re.findall(r'^  operation (\w+) = (\w+)\.operation$', body, re.M)
    expected = {'reserve': 'Reserve', 'readOutcome': 'Read', 'cancel': 'Cancel'}
    assert len(clauses) == len(expected) and dict(clauses) == expected, 'missing or repeated concrete control certificate'
    return {'reserve_operation': 'reserve', 'operation_outcome': 'readOutcome', 'cancel_operation': 'cancel'}


def check_public_tools(coverage):
    formal = formal_public_operations(read('spec/Mimir/ToolCatalog.agda'))
    native = native_public_operations(read('crates/core/src/operation_catalogue.rs'))
    dispatcher = read('crates/mcp/src/main.rs')
    assert '.extend(learning::tools())' in dispatcher, 'learning descriptors are not advertised'
    assert '.extend(operation_protocol::descriptors())' in dispatcher, 'control descriptors are not advertised'
    advertised = []
    for source in ['crates/mcp/src/main.rs', 'crates/mcp/src/learning.rs',
                   'crates/mcp/src/operation_protocol.rs']:
        advertised += re.findall(r'"name"\s*:\s*"([a-z_]+)"\s*,\s*"description"\s*:', read(source))
    documented = [item['name'] for item in coverage['mcp']]
    assert len(advertised) == len(set(advertised)), 'repeated advertised tool'
    assert len(documented) == len(set(documented)), 'repeated documented tool'
    assert set(documented) == set(formal) == set(native) == set(advertised), 'public tool sets disagree'
    assert coverage['counts']['mcp'] == len(native), 'documented public tool count is stale'
    for name, (group, boundaries) in native.items():
        expected = 'operationControl' if group == 'control' else ('businessWrite' if boundaries else 'readOnly')
        assert formal[name] == expected, ('public token/dispatch role disagrees', name)
    certificates = concrete_control_certificates(read('spec/Mimir/OperationControls.agda'))
    assert set(certificates) == {name for name, (group, _) in native.items() if group == 'control'}, 'control certificates disagree with public controls'
    entries = {item['name']: item for item in coverage['mcp']}
    for name, request in certificates.items():
        assert entries[name]['recovery_certificate'] == 'Mimir.OperationControls.Controls.operation ' + request, ('missing concrete control coverage', name)
    return len(native)


def native_cli_commands():
    main = 'crates/cli/src/main.rs'
    commands = [kebab(name) for name in enum_variants(main, 'Command')
                if name not in ['Operation', 'Config', 'Judge', 'Evidence', 'Delete', 'Doc', 'Hook']]
    for prefix, enum, source in [
        ('operation', 'Command', 'crates/cli/src/operations.rs'),
        ('config', 'Command', 'crates/cli/src/configuration.rs'),
        ('evidence', 'EvidenceCmd', main), ('delete', 'DeleteCmd', main),
        ('doc', 'DocCmd', main), ('hook', 'HookEvent', main),
        ('judge', 'JudgeCommand', 'crates/cli/src/judge/mod.rs'),
    ]:
        commands += [prefix + ' ' + kebab(name) for name in enum_variants(source, enum)]
    assert len(commands) == len(set(commands)), 'repeated CLI leaf'
    return commands


def formal_control_operations(source):
    body = source.split('  registered =', 1)[1].split('  lookup :', 1)[0]
    entries = re.findall(r'^\s*entry "([a-z_]+)" ([^\n]+)', body, re.M)
    operations = {}
    for name, declaration in entries:
        assert name not in operations, ('duplicate formal registered operation', name)
        assert re.fullmatch(r'(?:\[\]|\((?:(?:once|repeated) "[^"]+" ∷ )+\[\]\)) ∷', declaration), ('unsupported formal boundary declaration', name)
        operations[name] = [(site, mode == 'repeated') for mode, site in re.findall(r'(once|repeated) "([^"]+)"', declaration)]
    assert operations, 'missing concrete control catalogue'
    return operations


def native_struct_fields(source, name):
    body = re.search(r'\bstruct ' + re.escape(name) + r'\s*\{([^}]+)\}', source, re.S)
    assert body, ('missing native stored schema', name)
    return set(re.findall(r'^\s*(?:pub(?:\([^)]*\))?\s+)?(\w+)\s*:', body.group(1), re.M))


def formal_field_names(source, name):
    body = re.search(r'^  ' + re.escape(name) + r' =([^\n]*(?:\n    [^\n]+)*)', source, re.M)
    assert body, ('missing formal stored schema', name)
    return set(re.findall(r'toList "([a-z_]+)"', body.group(1)))


def check():
    coverage = json.loads(read('docs/FORMAL-BEHAVIOR-COVERAGE.json'))
    inventory = json.loads(read('docs/FORMAL-INVENTORY.json'))
    public_count = check_public_tools(coverage)

    controls = read('spec/Mimir/OperationControls.agda')
    native_catalogue = read('crates/core/src/operation_catalogue.rs')
    assert native_registered_operations(native_catalogue) == formal_control_operations(controls), 'operation-control plan catalogue disagrees with native registration'
    assert native_struct_fields(read('crates/core/src/store/operation_plans.rs'), 'StoredPlan') == formal_field_names(controls, 'fieldNames'), 'operation-control plan fields disagree with native storage'
    capture_source = read('crates/core/src/store/backfill.rs')
    assert native_struct_fields(capture_source, 'Capture') == formal_field_names(controls, 'captureFieldNames'), 'captured-selection fields disagree with native storage'
    assert native_struct_fields(capture_source, 'BackfillSource') == formal_field_names(controls, 'sourceFieldNames'), 'captured-source fields disagree with native storage'

    commands = native_cli_commands()
    cli_names = [item['name'] for item in coverage['cli']]
    assert len(cli_names) == len(set(cli_names)) == coverage['counts']['cli_leaves'], 'documented CLI count is stale'
    assert set(commands) == set(cli_names), {
        'unmapped_native_cli': sorted(set(commands) - set(cli_names)),
        'missing_native_cli': sorted(set(cli_names) - set(commands)),
    }

    files = list((ROOT / 'spec').rglob('*.agda'))
    module_paths = {'.'.join(p.relative_to(ROOT / 'spec').with_suffix('').parts): p for p in files}
    reached = set()

    def visit(name):
        if name in reached or name not in module_paths:
            return
        reached.add(name)
        source = module_paths[name].read_text()
        for dependency in re.findall(r'\bimport\s+(Mimir(?:\.[A-Za-z0-9_]+)*)', source):
            assert dependency in module_paths, (name, dependency)
            visit(dependency)

    visit('Mimir')
    assert reached == set(module_paths), sorted(set(module_paths) - reached)
    for path in files:
        source = path.read_text()
        assert re.search(r'\{-#\s*OPTIONS\s+[^#]*--safe\b', source), path
        # Remove line comments before scanning. This is an escape-marker audit;
        # the type checker is the authority for safety, holes and termination.
        code = '\n'.join(line.split('--', 1)[0] for line in source.splitlines())
        assert not re.search(r'\bpostulate\b|\bTERMINATING\b|\bNON_TERMINATING\b|allow-unsolved|\{!', code), path

    referenced = set()
    for category in ['mcp', 'cli', 'lifecycles']:
        for item in coverage[category]:
            assert item['completion_modules'], item['name']
            referenced.update(item['completion_modules'])
    for item in coverage['core_library']:
        referenced.update(item['modules'])
    for entry in inventory['files']:
        assert (ROOT / entry['path']).exists(), entry['path']
        if entry['classification'] == 'production-behavior':
            assert entry['behavioral_specification'], entry['path']
            referenced.update(entry['behavioral_specification'])
    for path in referenced:
        assert (ROOT / path).exists(), path
        assert '.'.join(Path(path).relative_to('spec').with_suffix('').parts) in reached, path

    bound_sources = {key: json.loads(value).strip() for key, value in re.findall(
        r'^source Schema\.(\w+) = toList (".*")$', read('spec/Mimir/MigrationScriptBinding.agda'), re.M)}
    migration_keys = ['initial', 'searchPath', 'embeddingTable', 'evidenceEdges',
                      'betaBeliefs', 'learning', 'candidates', 'assessment', 'owners', 'allocation',
                      'reviewQueueNotifications', 'operationReservations', 'operationBindings', 'operationStepReplies', 'operationPlans', 'operationRequestKeys', 'candidateKeyContent', 'embeddingOwners', 'operationCancellations', 'decayAccounting', 'firstDefeatClock', 'backfillChangeEvents', 'beliefSources', 'reviewPreparationEvents']
    sql_files = sorted((ROOT / 'crates/core/migrations').glob('*.sql'))
    assert len(sql_files) == len(migration_keys) == len(bound_sources)
    for path, key in zip(sql_files, migration_keys):
        assert embedded_sql_body(path.read_text()) == bound_sources[key], path

    return {
        'result': 'passed', 'mcp_operations': public_count,
        'cli_leaves': len(cli_names), 'lifecycle_groups': len(coverage['lifecycles']),
        'source_artifacts': len(inventory['files']),
        'production_artifacts': sum(x['classification'] == 'production-behavior' for x in inventory['files']),
        'safe_modules': len(files), 'root_reachable_modules': len(reached),
        'referenced_modules': len(referenced), 'exact_migration_bodies': len(sql_files),
        'boundary': 'Inventory and structural audit; Agda checking and Rust correspondence are separate.'
    }


if __name__ == '__main__':
    print(json.dumps(check(), indent=2))
