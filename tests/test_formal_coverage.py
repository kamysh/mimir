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


if __name__ == '__main__':
    unittest.main()
