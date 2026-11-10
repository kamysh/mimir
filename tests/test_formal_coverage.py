"""Check that source bindings compare the SQL the migration loader retains."""
import importlib.util
from pathlib import Path
import unittest
import json
from unittest.mock import patch


REPO = Path(__file__).resolve().parents[1]
spec = importlib.util.spec_from_file_location('formal_coverage', REPO / 'scripts/formal/check-coverage.py')
coverage = importlib.util.module_from_spec(spec)
spec.loader.exec_module(coverage)


class MigrationBodyTests(unittest.TestCase):
    header = '-- #!migration\n-- name: "upgrade",\n-- description: "Keep old IDs";\n'

    def test_sql_comments_after_metadata_are_preserved(self):
        body = "-- Keep old IDs.\nINSERT INTO owners SELECT * FROM history;"
        self.assertEqual(coverage.embedded_sql_body(self.header + '\n' + body + '\n'), body)

    def test_semicolon_in_metadata_does_not_end_header(self):
        source = self.header.replace('Keep old IDs', 'Keep old IDs; add a default')
        self.assertEqual(coverage.embedded_sql_body(source + 'SELECT 1;'), 'SELECT 1;')

    def test_body_semicolons_and_comments_are_not_rewritten(self):
        body = "DO $$ BEGIN PERFORM f(); END $$;\n-- Another statement.\nSELECT ';';"
        self.assertEqual(coverage.embedded_sql_body(self.header + body), body)

    def test_requires_array_is_metadata(self):
        source = self.header.replace('IDs";', 'IDs",\n-- requires: ["initial", "owners"];')
        self.assertEqual(coverage.embedded_sql_body(source + '-- SQL comment\nSELECT 1;'),
                         '-- SQL comment\nSELECT 1;')

    def test_unterminated_header_is_refused(self):
        with self.assertRaises(ValueError):
            coverage.embedded_sql_body(self.header.replace('IDs";', 'IDs",') + 'SELECT 1;')

    def test_missing_required_metadata_is_refused(self):
        with self.assertRaises(ValueError):
            coverage.embedded_sql_body('-- #!migration\n-- name: "upgrade";\nSELECT 1;')

    def test_second_migration_is_refused(self):
        with self.assertRaises(ValueError):
            coverage.embedded_sql_body(self.header + 'SELECT 1;\n' + self.header + 'SELECT 2;')

    def test_changed_comment_breaks_source_binding(self):
        source = self.header + '-- Keep old IDs.\nSELECT 1;'
        self.assertNotEqual(coverage.embedded_sql_body(source),
                            coverage.embedded_sql_body(source.replace('Keep old IDs.', 'Replace IDs.')))


class IntendedOutcomeContractTests(unittest.TestCase):
    def setUp(self):
        self.contract = json.loads(coverage.read('docs/intended-outcome-contract.schema.json'))

    def check_changed(self, change):
        change(self.contract)
        original_read = coverage.read
        with patch.object(coverage, 'read', side_effect=lambda path:
                          json.dumps(self.contract) if path == 'docs/intended-outcome-contract.schema.json'
                          else original_read(path)):
            coverage.check_intended_outcome_contract()

    def test_every_current_entry_has_an_intent_obligation(self):
        self.assertEqual(coverage.check_intended_outcome_contract(), 41)

    def test_a_missing_operation_fails_coverage(self):
        with self.assertRaises(AssertionError):
            self.check_changed(lambda contract: contract['x-intent-adapters'][0]['operations'].remove('delete_project'))

    def test_a_missing_saved_answer_table_fails_coverage(self):
        with self.assertRaises(AssertionError):
            self.check_changed(lambda contract: contract['$defs']['operations']['properties'].pop('savedReplies'))

    def test_body_only_result_cannot_replace_complete_public_payload(self):
        with self.assertRaises(AssertionError):
            self.check_changed(lambda contract: contract['$defs']['output']['properties'].pop('public_payload'))

    def test_execution_receipts_cannot_be_omitted_from_the_snapshot(self):
        with self.assertRaises(AssertionError):
            self.check_changed(lambda contract: contract['$defs']['operations']['properties'].pop('executions'))

    def test_physical_stop_timestamp_cannot_be_omitted(self):
        with self.assertRaises(AssertionError):
            self.check_changed(lambda contract: contract['$defs']['execution']['properties'].pop('stoppedAt'))

    def test_execution_record_coverage_cannot_be_disabled(self):
        with self.assertRaises(AssertionError):
            self.check_changed(lambda contract: contract['x-model-records'].remove(
                {'definition': 'execution', 'module': 'ApplicationStore', 'record': 'ExecutionRow'}))

    def test_cli_statistics_and_library_pattern_reads_cannot_be_skipped(self):
        for name in ('stats', 'get_pattern'):
            with self.subTest(name=name):
                self.setUp()
                family = next(item for item in self.contract['x-intent-adapters']
                              if name in item['operations'])
                with self.assertRaises(AssertionError):
                    self.check_changed(lambda contract: family['operations'].remove(name))

    def test_observed_final_world_cannot_be_an_expected_input(self):
        with self.assertRaises(AssertionError):
            self.check_changed(lambda contract: contract['$defs']['input']['properties'].update({'observed_world': {}}))


class OperationControlCatalogueTests(unittest.TestCase):
    def setUp(self):
        self.native = (REPO / 'crates/core/src/operation_catalogue.rs').read_text()
        self.formal = (REPO / 'spec/Mimir/OperationControls.agda').read_text()

    def test_internal_operations_and_repeated_sites_match_the_same_catalogue(self):
        self.assertEqual(coverage.native_registered_operations(self.native),
                         coverage.formal_control_operations(self.formal))

    def test_an_undeclared_internal_name_cannot_be_silently_ignored(self):
        changed = self.native.replace(
            '.or_else(|| (name == "delete_evidence").then_some(Self::DeleteEvidence))',
            '.or_else(|| (name == "delete_evidence").then_some(Self::DeleteEvidence))\n'
            '            .or_else(|| (name == "undeclared_alias").then_some(Self::DeleteEvidence))')
        self.assertNotEqual(changed, self.native)
        with self.assertRaises(AssertionError):
            coverage.native_registered_operations(changed)

    def test_duplicate_formal_entries_are_rejected(self):
        original = next(line for line in self.formal.splitlines() if 'entry "insert_belief"' in line)
        changed = self.formal.replace(original, original + '\n' + original)
        with self.assertRaises(AssertionError):
            coverage.formal_control_operations(changed)

    def test_repeated_and_single_sites_cannot_be_interchanged(self):
        current = self.formal.split('  registered =', 1)[1].split('  lookup :', 1)[0]
        original = next(line for line in current.splitlines()
                        if 'entry "sweep_expired_defeated"' in line)
        replacement = original.replace('once "store.delete_belief"', 'repeated "store.delete_belief"')
        if replacement == original:
            replacement = original.replace('repeated "store.delete_belief"', 'once "store.delete_belief"')
        changed = self.formal.replace(original, replacement, 1)
        self.assertNotEqual(changed, self.formal)
        self.assertNotEqual(coverage.native_registered_operations(self.native),
                            coverage.formal_control_operations(changed))

    def test_nested_snapshot_schema_names_do_not_leak_into_outer_plan_fields(self):
        source = (REPO / 'crates/core/src/store/operation_plans.rs').read_text()
        self.assertEqual(coverage.native_struct_fields(source, 'StoredPlan'),
                         coverage.formal_field_names(self.formal, 'fieldNames'))
        capture = (REPO / 'crates/core/src/store/backfill.rs').read_text()
        self.assertEqual(coverage.native_struct_fields(capture, 'BackfillSource'),
                         coverage.formal_field_names(self.formal, 'sourceFieldNames'))
        self.assertEqual(coverage.native_struct_fields(capture, 'Capture'),
                         coverage.formal_field_names(self.formal, 'captureFieldNames'))


class PublicToolCoverageTests(unittest.TestCase):
    def setUp(self):
        self.native = (REPO / 'crates/core/src/operation_catalogue.rs').read_text()
        self.formal = (REPO / 'spec/Mimir/ToolCatalog.agda').read_text()
        self.controls = (REPO / 'spec/Mimir/OperationControls.agda').read_text()
        self.manifest = json.loads((REPO / 'docs/FORMAL-BEHAVIOR-COVERAGE.json').read_text())

    def test_every_advertised_control_has_its_concrete_certificate(self):
        native = coverage.native_public_operations(self.native)
        controls = {name for name, (group, _) in native.items() if group == 'control'}
        self.assertEqual(controls, set(coverage.concrete_control_certificates(self.controls)))
        self.assertEqual(coverage.check_public_tools(self.manifest), len(native))

    def test_controls_do_not_become_business_saved_plans(self):
        public = coverage.native_public_operations(self.native)
        registered = coverage.native_registered_operations(self.native)
        for name, (group, _) in public.items():
            self.assertEqual(name in registered, group != 'control')
        changed = self.native.replace('!matches!(operation, Operation::Control(_))', 'true')
        with self.assertRaises(AssertionError):
            coverage.native_registered_operations(changed)

    def test_missing_control_descriptor_is_not_covered_by_its_native_registration(self):
        original_read = coverage.read
        def without_controls(path):
            return '' if path == 'crates/mcp/src/operation_protocol.rs' else original_read(path)
        with patch.object(coverage, 'read', without_controls), self.assertRaises(AssertionError):
            coverage.check_public_tools(self.manifest)

    def test_unused_control_descriptors_do_not_count_as_advertised(self):
        original_read = coverage.read
        def disconnected(path):
            source = original_read(path)
            return source.replace('.extend(operation_protocol::descriptors())', '') if path == 'crates/mcp/src/main.rs' else source
        with patch.object(coverage, 'read', disconnected), self.assertRaises(AssertionError):
            coverage.check_public_tools(self.manifest)

    def test_missing_concrete_control_proof_is_rejected(self):
        changed = self.controls.replace('  operation cancel = Cancel.operation\n', '')
        self.assertNotEqual(changed, self.controls)
        with self.assertRaises(AssertionError):
            coverage.concrete_control_certificates(changed)

    def test_repeated_concrete_control_proof_is_rejected(self):
        changed = self.controls.replace('  operation cancel = Cancel.operation',
                                        '  operation cancel = Cancel.operation\n  operation cancel = Cancel.operation')
        with self.assertRaises(AssertionError):
            coverage.concrete_control_certificates(changed)

    def test_new_native_group_is_not_silently_ignored(self):
        changed = self.native.replace('    control {', '    administration {')
        with self.assertRaises(AssertionError):
            coverage.native_public_operations(changed)

    def test_changed_writer_token_role_is_rejected(self):
        original_read = coverage.read
        def changed_role(path):
            source = original_read(path)
            return source.replace('kind insertBelief = businessWrite', 'kind insertBelief = readOnly') if path == 'spec/Mimir/ToolCatalog.agda' else source
        with patch.object(coverage, 'read', changed_role), self.assertRaises(AssertionError):
            coverage.check_public_tools(self.manifest)

    def test_closed_tool_without_wire_or_kind_clause_is_rejected(self):
        changed = self.formal.replace('queryLearningContext : Tool', 'queryLearningContext forgottenTool : Tool')
        with self.assertRaises(AssertionError):
            coverage.formal_public_operations(changed)

    def test_cli_control_leaves_are_discovered_without_treating_group_as_leaf(self):
        commands = coverage.native_cli_commands()
        self.assertNotIn('operation', commands)
        self.assertTrue({'operation reserve', 'operation outcome', 'operation cancel'} <= set(commands))


class CliControlCorrespondenceTests(unittest.TestCase):
    def test_each_cli_control_selects_the_same_service_action_as_its_mcp_tool(self):
        self.assertEqual(set(coverage.cli_control_correspondence()),
                         {'operation ' + coverage.kebab(name) for name in
                          coverage.enum_variants('crates/cli/src/operations.rs', 'Command')})

    def test_reading_an_outcome_cannot_silently_select_cancellation(self):
        original_read = coverage.read
        def wrong_operation(path):
            source = original_read(path)
            return source.replace('controlTool outcome = Tools.operationOutcome',
                                  'controlTool outcome = Tools.cancelOperation') if path == 'spec/Mimir/CLI.agda' else source
        with patch.object(coverage, 'read', wrong_operation), self.assertRaises(AssertionError):
            coverage.cli_control_correspondence()

    def test_a_changed_native_cli_action_cannot_keep_the_old_formal_mapping(self):
        original_read = coverage.read
        def wrong_action(path):
            source = original_read(path)
            return source.replace('service.read_operation_outcome(token, None)',
                                  'service.cancel_operation(token)') if path == 'crates/cli/src/operations.rs' else source
        with patch.object(coverage, 'read', wrong_action), self.assertRaises(AssertionError):
            coverage.cli_control_correspondence()

    def test_missing_formal_control_arm_is_rejected(self):
        original_read = coverage.read
        def missing_control(path):
            source = original_read(path)
            return source.replace('  controlTool cancel = Tools.cancelOperation\n', '') if path == 'spec/Mimir/CLI.agda' else source
        with patch.object(coverage, 'read', missing_control), self.assertRaises(AssertionError):
            coverage.cli_control_correspondence()
class ApplicationAssemblyTests(unittest.TestCase):
    def setUp(self):
        self.source = (REPO / 'spec/Mimir/ApplicationProtocol.agda').read_text()

    def reject_mutation(self, old, new):
        self.assertEqual(self.source.count(old), 1)
        with self.assertRaises(AssertionError):
            coverage.check_application_assembly(self.source.replace(old, new, 1))

    def test_actual_assembly_selects_checked_state_and_terminal_history(self):
        result = coverage.check_application_assembly(self.source)
        self.assertEqual(result['state_constructors'], ['running'])
        self.assertEqual(result['result_constructor'], 'terminalResult')

    def test_extra_raw_script_state_constructor_is_rejected(self):
        self.reject_mutation('      Checked.RunState call (input call) initial → State',
                             '      Checked.RunState call (input call) initial → State\n'
                             '    rawScript : O.E.Script call Wire.Value → State')

    def test_raw_success_result_constructor_is_rejected(self):
        self.reject_mutation('  record Result : Set where\n    constructor terminalResult',
                             '  data Result : Set where\n    rawSuccess : Wire.Value → Result\n'
                             '    constructor terminalResult')

    def test_raw_result_cannot_replace_terminal_history(self):
        self.reject_mutation('      terminal : Checked.Terminal call (input call) initial',
                             '      terminal : Wire.Value')

    def test_operation_cannot_skip_its_computed_certificate(self):
        self.reject_mutation('  operation call = routeOperation (route call) (certificate call)',
                             '  operation call = suppliedOperation call')

    def test_state_checker_cannot_take_an_independent_operation(self):
        self.reject_mutation('Recovery.CheckedFor (operation call) (RouteSuccess (route call))',
                             'Recovery.CheckedFor suppliedOperation (RouteSuccess (route call))')

    def test_writer_cannot_select_the_bare_body_route(self):
        self.reject_mutation('... | Tools.businessWrite = registeredRoute (Creating.submittedWrite tool submitted)',
                             '... | Tools.businessWrite = plainRoute (choice call)')

    def test_registered_certificate_cannot_be_caller_selected(self):
        self.reject_mutation('  routeCertificate (registeredRoute requested) = WriteFixed.operation requested',
                             '  routeCertificate (registeredRoute requested) = suppliedCertificate requested')

    def test_existing_expected_shape_in_comments_does_not_hide_an_escape(self):
        old = '      Checked.RunState call (input call) initial → State'
        self.reject_mutation(old, old + '\n    -- raw scripts are checked elsewhere\n'
                             '    unchecked : O.E.Script call Wire.Value → State')

    def test_matching_declarations_in_another_module_do_not_cover_run(self):
        changed = self.source.replace('module Run (environment : Environment) where',
                                      'module UnusedCheckedAssembly (environment : Environment) where', 1)
        changed += '\nmodule Run (environment : Environment) where\n' \
                   '  module Unchecked where\n' \
                   '    data State : Set where\n' \
                   '      rawScript : Wire.Value → State\n' \
                   '  open Unchecked public\n'
        with self.assertRaises(AssertionError):
            coverage.check_application_assembly(changed)

    def test_whitespace_and_line_comments_are_not_semantic_evidence(self):
        changed = self.source.replace('    constructor terminalResult',
                                      '    constructor    terminalResult -- retained checked history')
        self.assertEqual(coverage.check_application_assembly(self.source),
                         coverage.check_application_assembly(changed))


if __name__ == '__main__':
    unittest.main()
