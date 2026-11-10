#!/usr/bin/env python3
"""Compare complete, already typed/canonicalized recovery observations.

The expected file must be produced by the Agda intended-outcome adapter, not
by a successful native run. This comparator does not implement that adapter or
validate its domain records. Physical table order is canonicalized by the same
snapshot adapter on both sides; this comparison never sorts stored arrays.
"""

import argparse
from decimal import Decimal
import json
from pathlib import Path
import sys


OUTCOME_FIELDS = {'world', 'body_result', 'public_payload'}


def unique_object(pairs):
    result = {}
    for key, value in pairs:
        if key in result:
            raise ValueError(f'duplicate JSON field: {key!r}')
        result[key] = value
    return result


def reject_constant(value):
    raise ValueError(f'non-finite JSON number: {value}')


def load_observation(path, *, native=False):
    value = json.loads(Path(path).read_text(), object_pairs_hook=unique_object,
                       parse_float=Decimal, parse_constant=reject_constant)
    fields = OUTCOME_FIELDS | ({'exchange'} if native else set())
    if not isinstance(value, dict) or set(value) != fields:
        raise ValueError(f'{path}: required complete observation fields: {sorted(fields)}')
    return {key: value[key] for key in OUTCOME_FIELDS}


def number(value):
    return isinstance(value, (int, Decimal)) and not isinstance(value, bool)


def negative_zero(value):
    return isinstance(value, Decimal) and value.is_zero() and value.is_signed()


def differences(expected, actual, path=()):
    """Yield every difference; omission, null and array order remain distinct."""
    if number(expected) and number(actual):
        if expected != actual or negative_zero(expected) != negative_zero(actual):
            yield path, 'number', expected, actual
    elif type(expected) is not type(actual):
        yield path, 'type', expected, actual
    elif isinstance(expected, dict):
        for key in sorted(expected.keys() | actual.keys()):
            if key not in expected:
                yield path + (key,), 'unexpected field', None, actual[key]
            elif key not in actual:
                yield path + (key,), 'missing field', expected[key], None
            else:
                yield from differences(expected[key], actual[key], path + (key,))
    elif isinstance(expected, list):
        if len(expected) != len(actual):
            yield path, 'array length', len(expected), len(actual)
        for index, (left, right) in enumerate(zip(expected, actual)):
            yield from differences(left, right, path + (index,))
    elif expected != actual:
        yield path, 'value', expected, actual


def pointer(path):
    return ''.join('/' + str(part).replace('~', '~0').replace('/', '~1')
                   for part in path) or '/'


def compare_files(expected_path, native_path):
    expected = load_observation(expected_path)
    actual = load_observation(native_path, native=True)
    return list(differences(expected, actual))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--expected', required=True, type=Path,
                        help='retained output from the actual Agda intent adapter')
    parser.add_argument('--observed', required=True, type=Path,
                        help='retained complete native observation including exchange')
    args = parser.parse_args()
    try:
        mismatches = compare_files(args.expected, args.observed)
    except (OSError, ValueError) as error:
        print(f'Cannot compare complete outcomes: {error}', file=sys.stderr)
        return 2
    for path, reason, expected, actual in mismatches:
        print(f'{pointer(path)}: {reason}\n  expected: {expected!r}\n  observed: {actual!r}')
    if mismatches:
        print(f'{len(mismatches)} differences; inputs retained at '
              f'{args.expected} and {args.observed}')
        return 1
    print('Complete world, body result and public payload match.')
    return 0


if __name__ == '__main__':
    sys.exit(main())
