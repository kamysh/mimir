import importlib.util
import json
from pathlib import Path
import tempfile
import unittest


MODULE_PATH = Path(__file__).resolve().parents[1] / 'scripts/formal/compare-outcomes.py'
SPEC = importlib.util.spec_from_file_location('outcome_comparison', MODULE_PATH)
comparison = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(comparison)


class CompleteOutcomeComparisonTests(unittest.TestCase):
    def compare_json(self, expected, actual):
        decode = lambda value: json.loads(value, parse_float=comparison.Decimal)
        return list(comparison.differences(decode(expected), decode(actual)))

    def test_equal_number_spellings_do_not_hide_a_value_change(self):
        self.assertEqual(self.compare_json('1.00', '1e0'), [])
        self.assertTrue(self.compare_json('0.10000000000000001', '0.1'))

    def test_vectors_keep_sign_of_zero_and_all_components(self):
        self.assertTrue(self.compare_json('[-0.0, 1]', '[0.0, 1]'))
        self.assertTrue(self.compare_json('[0, 1]', '[0, 1, 2]'))

    def test_boolean_is_not_a_number(self):
        self.assertTrue(self.compare_json('true', '1'))

    def test_missing_null_and_empty_are_different(self):
        for actual in ('{}', '{"source":[]}', '{"source":""}'):
            with self.subTest(actual=actual):
                self.assertTrue(self.compare_json('{"source":null}', actual))

    def test_object_member_order_is_irrelevant_but_array_order_matters(self):
        self.assertEqual(self.compare_json('{"a":1,"b":2}', '{"b":2,"a":1}'), [])
        self.assertTrue(self.compare_json('[1,2]', '[2,1]'))

    def test_large_ids_and_long_diagnostic_tails_are_not_lost(self):
        self.assertTrue(self.compare_json(str(2 ** 128 - 1), str(2 ** 128 - 2)))
        prefix = 'source detail ' * 10000
        self.assertTrue(self.compare_json(json.dumps(prefix + 'A'), json.dumps(prefix + 'B')))

    def test_every_difference_is_reported_with_an_unambiguous_path(self):
        result = self.compare_json('{"a/b~":[1,2],"missing":3}', '{"a/b~":[9,8],"extra":4}')
        self.assertEqual([comparison.pointer(item[0]) for item in result],
                         ['/a~1b~0/0', '/a~1b~0/1', '/extra', '/missing'])

    def test_complete_observation_requires_world_body_and_public_reply(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            expected = root / 'expected.json'
            native = root / 'native.json'
            outcome = {'world': {}, 'body_result': {'kind': 'not_entered'},
                       'public_payload': {'status': 'needs_input'}}
            expected.write_text(json.dumps(outcome))
            native.write_text(json.dumps(outcome | {'exchange': {'stdout': 'retained'}}))
            self.assertEqual(comparison.compare_files(expected, native), [])
            native.write_text(json.dumps(outcome | {'public_payload': None, 'exchange': {}}))
            self.assertTrue(comparison.compare_files(expected, native))
            expected.write_text(json.dumps({'world': {}}))
            with self.assertRaises(ValueError):
                comparison.compare_files(expected, native)

    def test_duplicate_fields_and_nonfinite_numbers_are_rejected(self):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / 'bad.json'
            for value in ('{"world":{},"world":{}}', 'NaN', 'Infinity', '-Infinity'):
                with self.subTest(value=value):
                    path.write_text(value)
                    with self.assertRaises(ValueError):
                        comparison.load_observation(path)

    def test_deleted_belief_does_not_conceal_its_remaining_vector(self):
        result = self.compare_json(
            '{"beliefs":[],"beliefVectors":[]}',
            '{"beliefs":[],"beliefVectors":[{"id":"original","vector":[1,0]}]}')
        self.assertEqual(result[0][0], ('beliefVectors',))

    def test_a_stop_acknowledgement_cannot_be_replaced_with_elapsed_time(self):
        result = self.compare_json(
            '{"executions":[{"identity":1,"stoppedAt":7}]}',
            '{"executions":[{"identity":1,"stoppedAt":null}]}')
        self.assertEqual(result[0][0], ('executions', 0, 'stoppedAt'))


if __name__ == '__main__':
    unittest.main()
