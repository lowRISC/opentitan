#!/usr/bin/env python3
# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

import argparse
import json
import math
import sys

import hjson


def parse_hex_int(hex_str):
    # int() throws an error message for empty string
    if hex_str == '':
        return 0
    return int(hex_str, 16)


def parse_test(raw_data, n, e, t):
    test = {'n': n, 'e': e}

    test['msg'] = parse_hex_int(t['msg'])

    # Message is expressed in hex notation, so the length in bytes is
    # the number of characters / 2
    test['msg_len'] = math.ceil(len(t['msg']) / 2)

    test['signature'] = parse_hex_int(t['sig'])

    notes = []
    if t['comment']:
        notes.append(t['comment'])
    # Add notes from flags, if any
    notes.extend([raw_data['notes'][flag] for flag in t['flags']])

    # cases for expected result
    if t['result'] == 'valid':
        test['valid'] = True
    elif t['result'] == 'invalid':
        test['valid'] = False
    elif t['result'] == 'acceptable':
        # err on the side of caution and reject "acceptable" signatures
        test['valid'] = False
        notes.append('signature marked as acceptable by wycheproof')
    else:
        raise RuntimeError('Unexpected result type {}'.format(test['result']))

    test['comment'] = 'wycheproof test with tcId={:d}, notes={}'.format(
        t["tcId"], ', '.join(notes))

    return test


def parse_test_group(raw_data, group):
    tests = []
    n = parse_hex_int(group['n'])
    e = parse_hex_int(group['e'])
    for t in group['tests']:
        tests.append(parse_test(raw_data, n, e, t))
    return tests


def parse_test_vectors(raw_data):
    if raw_data['algorithm'] != 'RSASSA-PKCS1-v1_5':
        raise RuntimeError('Unexpected algorithm: {}, expected {}'.format(
            raw_data['algorithm'], 'RSASSA-PKCS1-v1_5'))
    tests = []
    for group in raw_data['testGroups']:
        if group['sha'] != 'SHA-256':
            raise RuntimeError(
                'Unexpected hash function: {}, expected {}'.format(
                    group['sha'], 'SHA-256'))
        tests.extend(parse_test_group(raw_data, group))
    return tests


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('src',
                        metavar='FILE',
                        type=argparse.FileType('r'),
                        help='Read test vectors from this JSON file.')
    parser.add_argument('dst',
                        metavar='FILE',
                        type=argparse.FileType('w'),
                        help='Write output to this file.')

    args = parser.parse_args()

    testvecs = parse_test_vectors(json.load(args.src))
    args.src.close()
    hjson.dump(testvecs, args.dst)
    args.dst.close()

    return 0


if __name__ == '__main__':
    sys.exit(main())
