#!/usr/bin/env python3
# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

'''Parses the `.rsp` file for a SPHINCS+ KAT into hjson.

The KAT files are included with the SPHINCS+ NIST competition submissions,
which can be downloaded here: https://sphincs.org/resources.html

The expected test format is:
count = 0
seed = 061550234D158C5EC9<...more hex, clipped...>
mlen = 33
msg = D81C4D8D734FCBFBEADE3D3F8A039FAA2A2C9957E835AD55B22E75BF57BB556AC8
pk = B505D7CFAD1B497499323C8686325E47FD65CBB2867A44C3D67ACC840ACF609F
sk = 7C9935A0B07694AA0C<...more hex, clipped...>
smlen = 7889
sm = 07EB19E7D838D71EF6<...more hex, clipped...>

The tests are expected to be separated by newlines. The `sm` parameter is the
signature concatenated with the message.
'''

import argparse
import hjson
import math
import os
import sys


def parse_single_test(test_string):
    fields = {}
    for field in test_string.split('\n'):
        name_value = field.split(' = ')
        if len(name_value) != 2:
            raise ValueError(f'Could not parse field: {field}')
        name, value = name_value
        fields[name] = value

    # Parse the signature from `sm` by removing the message from the end.
    sig = fields['sm'][:-len(fields['msg'])]
    assert sig + fields['msg'] == fields['sm']

    # Compute the length (in bytes) of the signature.
    msg_len = int(fields['mlen'])
    sm_len = int(fields['smlen'])
    sig_len = sm_len - msg_len

    return {'id': int(fields['count']),
            'seed_hex': fields['seed'],
            'msg_len': msg_len,
            'msg_hex': fields['msg'],
            'pk_hex': fields['pk'],
            'sk_hex': fields['sk'],
            'sig_len': sig_len,
            'sig_hex': sig,
            }


def parse_test_vectors(rspfile):
    # Split at "count = " lines (and remove the first element).
    tests = rspfile.read().split('count =')[1:]
    # Re-add "count = ". and remove whitespace.
    tests = [('count = ' + t).strip() for t in tests]
    return [parse_single_test(t) for t in tests]


def write_file(testvecs, filename):
    with open(filename, 'w') as dst:
        hjson.dump(testvecs, dst)
        # Insert newline at end of file (hjson.dump doesn't do this and the
        # linter checks complain otherwise).
        dst.write('\n')


def write_split(testvecs, filename, max_tests_per_file):
    dst_name, ext = os.path.splitext(filename)
    if dst_name == '' or ext == '':
        raise ValueError(f'Invalid destination file: {filename}')
    num_files = math.ceil(len(testvecs) / max_tests_per_file)
    for i in range(num_files):
        start = i * max_tests_per_file
        tests = testvecs[start:start + max_tests_per_file]
        write_file(tests, f'{dst_name}{i}{ext}')


def main() -> int:
    parser = argparse.ArgumentParser(
        description='Analyze whether secret data affects the control flow of '
        'an OTBN program or subroutine.')
    parser.add_argument('src',
                        metavar='FILE',
                        type=argparse.FileType('r'),
                        help='Read test vectors from this KAT .rsp file.')
    parser.add_argument('dst',
                        type=str,
                        help=(
                            'Write output to this HJSON file. If multiple '
                            'files are needed, they will be suffixed with an '
                            'index (e.g. foo0.hjson, foo1.hjson).'))
    parser.add_argument('--num-tests',
                        type=int,
                        required=False,
                        help=('Maximum number of tests per file.'))
    parser.add_argument('--test-start-index',
                        type=int,
                        required=False,
                        default=0,
                        help=('Index of first test to parse (default=0).'))
    args = parser.parse_args()

    with args.src as src:
        testvecs = parse_test_vectors(src)

    testvecs = testvecs[args.test_start_index:]

    if args.num_tests is None or len(testvecs) <= args.num_tests:
        # Write output to a single file.
        write_file(testvecs, args.dst)
    else:
        # Write output to multiple files.
        write_split(testvecs, args.dst, args.num_tests)

    return 0


if __name__ == '__main__':
    sys.exit(main())
