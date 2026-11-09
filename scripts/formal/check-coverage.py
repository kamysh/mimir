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
    match = re.search(r'(?:pub )?enum ' + name + r' \{(.*?)\n\}', read(path), re.S)
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


def native_registered_operations(source):
    """Read the maintained closed catalogue, including non-MCP operations."""
    sites = dict(re.findall(r'Self::(\w+)\s*=>\s*"(store\.[^"]+)"', source))

    def boundaries(body):
        calls = re.findall(r'(once|repeated)\((\w+)\)', body)
        remainder = re.sub(r'(once|repeated)\(\w+\)', '', body)
        assert not remainder.strip(' ,\t\r\n'), ('unsupported boundary declaration', body)
        return [(sites[site], mode == 'repeated') for mode, site in calls]

    entries = re.findall(r'^\s*\w+\s*=>\s*"([a-z_]+)"\s*\[([^\n]*)\]', source, re.M)
    operations = {name: boundaries(body) for name, body in entries}
    assert operations and len(operations) == len(entries), 'missing or repeated operation declarations'
    private = source.split('impl RegisteredOperation {', 1)[1]
    names = dict(re.findall(r'Self::(\w+)\s*=>\s*"([a-z_]+)"', private))
    named = private.split('pub fn named', 1)[1].split('pub fn name(', 1)[0]
    assert set(re.findall(r'"([a-z_]+)"', named)) == set(names.values()), 'unmodelled named internal operation'
    for variant, name in names.items():
        match = re.search(r'Self::' + variant + r'\s*=>\s*\{\s*const PLAN:[^=]+=\s*&\[([^\]]*)\]', private)
        assert match, ('unsupported internal boundary declaration', variant)
        assert name not in operations, ('duplicate registered operation', name)
        operations[name] = boundaries(match.group(1))
    return operations


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
    formal_names = re.findall(r'^wireName\s+\w+\s*=\s*"([a-z_]+)"', read('spec/Mimir/ToolCatalog.agda'), re.M)
    advertised = []
    for source in ['crates/mcp/src/main.rs', 'crates/mcp/src/learning.rs']:
        advertised += re.findall(r'"name"\s*:\s*"([a-z_]+)"\s*,\s*"description"\s*:', read(source))
    operation_names = [item['name'] for item in coverage['mcp']]
    assert len(operation_names) == len(set(operation_names)) == 34
    assert set(operation_names) == set(formal_names) == set(advertised)

    controls = read('spec/Mimir/OperationControls.agda')
    native_catalogue = read('crates/core/src/operation_catalogue.rs')
    assert native_registered_operations(native_catalogue) == formal_control_operations(controls), 'operation-control plan catalogue disagrees with native registration'
    assert native_struct_fields(read('crates/core/src/store/operation_plans.rs'), 'StoredPlan') == formal_field_names(controls, 'fieldNames'), 'operation-control plan fields disagree with native storage'
    capture_source = read('crates/core/src/store/backfill.rs')
    assert native_struct_fields(capture_source, 'Capture') == formal_field_names(controls, 'captureFieldNames'), 'captured-selection fields disagree with native storage'
    assert native_struct_fields(capture_source, 'BackfillSource') == formal_field_names(controls, 'sourceFieldNames'), 'captured-source fields disagree with native storage'

    main = 'crates/cli/src/main.rs'
    commands = [kebab(name) for name in enum_variants(main, 'Command')
                if name not in ['Config', 'Judge', 'Evidence', 'Delete', 'Doc', 'Hook']]
    for prefix, enum, source in [
        ('config', 'Command', 'crates/cli/src/configuration.rs'),
        ('evidence', 'EvidenceCmd', main), ('delete', 'DeleteCmd', main),
        ('doc', 'DocCmd', main), ('hook', 'HookEvent', main),
        ('judge', 'JudgeCommand', 'crates/cli/src/judge/mod.rs'),
    ]:
        commands += [prefix + ' ' + kebab(name) for name in enum_variants(source, enum)]
    cli_names = [item['name'] for item in coverage['cli']]
    assert len(commands) == len(set(commands)) == len(cli_names) == coverage['counts']['cli_leaves']
    assert set(commands) == set(cli_names)

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
                      'reviewQueueNotifications', 'operationReservations', 'operationBindings', 'operationStepReplies', 'operationPlans', 'operationRequestKeys', 'candidateKeyContent', 'embeddingOwners', 'operationCancellations', 'decayAccounting', 'firstDefeatClock', 'backfillChangeEvents', 'beliefSources']
    sql_files = sorted((ROOT / 'crates/core/migrations').glob('*.sql'))
    assert len(sql_files) == len(migration_keys) == len(bound_sources)
    for path, key in zip(sql_files, migration_keys):
        assert embedded_sql_body(path.read_text()) == bound_sources[key], path

    return {
        'result': 'passed', 'mcp_operations': len(operation_names),
        'cli_leaves': len(cli_names), 'lifecycle_groups': len(coverage['lifecycles']),
        'source_artifacts': len(inventory['files']),
        'production_artifacts': sum(x['classification'] == 'production-behavior' for x in inventory['files']),
        'safe_modules': len(files), 'root_reachable_modules': len(reached),
        'referenced_modules': len(referenced), 'exact_migration_bodies': len(sql_files),
        'boundary': 'Inventory and structural audit; Agda checking and Rust correspondence are separate.'
    }


if __name__ == '__main__':
    print(json.dumps(check(), indent=2))
