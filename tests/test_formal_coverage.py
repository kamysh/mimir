"""Check that source bindings compare the SQL the migration loader retains."""
import importlib.util
from pathlib import Path
import unittest


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
        changed = self.formal.replace('repeated "store.delete_belief"', 'once "store.delete_belief"')
        self.assertNotEqual(changed, self.formal)
        self.assertNotEqual(coverage.native_registered_operations(self.native),
                            coverage.formal_control_operations(changed))

    def test_nested_snapshot_schema_names_do_not_leak_into_outer_plan_fields(self):
        source = (REPO / 'crates/core/src/store/operation_plans.rs').read_text()
        self.assertEqual(coverage.native_struct_fields(source, 'StoredPlan'),
                         coverage.formal_field_names(self.formal, 'fieldNames'))
        capture = (REPO / 'crates/core/src/store/backfill.rs').read_text()
        self.assertEqual(coverage.native_struct_fields(capture, 'Source'),
                         coverage.formal_field_names(self.formal, 'sourceFieldNames'))
        self.assertEqual(coverage.native_struct_fields(capture, 'Capture'),
                         coverage.formal_field_names(self.formal, 'captureFieldNames'))


if __name__ == '__main__':
    unittest.main()
