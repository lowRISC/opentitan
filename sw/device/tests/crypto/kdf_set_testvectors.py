#!/usr/bin/env python3
# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

import argparse
import sys

import hjson
from mako.template import Template

'''
Read in a JSON test vector file, convert the test vector to C constants, and
generate a header file with these test vectors.
'''


def str_to_hex_array(x, return_byte_array = True):
    '''Chop a given long hex string into an array of hex bytes or hex words.'''
    # Strip `0x` prefix
    x = x[2:]

    byte_list = []
    for i in range(0, len(x), 2):
        byte_list.append(x[i:i + 2])

    # Return a byte array if `return_byte_array` is True, else
    # return a word array
    if return_byte_array:
        return ["0x" + y for y in byte_list]

    if len(byte_list) % 4 != 0:
        raise ValueError(len(byte_list))

    word_list = []
    # Arrange words in little endian
    for i in range(-len(byte_list) + 3, 3, 4):
        word_list.append("".join(byte_list[i: i - 4: -1]))

    return ["0x" + y for y in word_list]


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument('--hjsonfile', '-j',
                        metavar='FILE',
                        required=True,
                        type=argparse.FileType('r'),
                        help='Read test vectors from this HJSON file.')
    parser.add_argument('--template', '-t',
                        metavar='FILE',
                        required=True,
                        type=argparse.FileType('r'),
                        help='Read header template from this file.')
    parser.add_argument('--headerfile', '-o',
                        metavar='FILE',
                        required=True,
                        type=argparse.FileType('w'),
                        help='Write output to this file.')

    args = parser.parse_args()
    # Read test vectors and stringify them
    testvecs = hjson.load(args.hjsonfile)
    args.hjsonfile.close()

    # Convert the message into an array of bytes
    for t in testvecs:
        # Rename some input args from KMAC to KDF convention
        t["key_derivation_key"] = t["key"]
        t["context"] = t["input_msg"]
        t["label"] = t["cust_str"]
        t["keying_material"] = t["digest"]

        if t["security_str"] == 128:
            t["test_operation"] = "kKdfTestOperationKmac128"
        elif t["security_str"] == 256:
            t["test_operation"] = "kKdfTestOperationKmac256"

        for dict_key in ["label", "context"]:
            if dict_key in t:
                t[dict_key] = str_to_hex_array(t[dict_key])

        # Keys need to be in word (uint32_t) granularity
        t["keyblob"] = str_to_hex_array(t["key_derivation_key"], return_byte_array = False)
        t["keyblob"] += ["0x00000000"] * len(t["keyblob"])

        # Derived key material also needs to have word granularity
        t["km_keyblob"] = str_to_hex_array(t["keying_material"], return_byte_array = False)
        t["km_keyblob"] += ["0x00000000"] * len(t["km_keyblob"])

    args.headerfile.write(Template(args.template.read()).render(tests=testvecs))
    args.headerfile.close()
    args.template.close()

    return 0


if __name__ == '__main__':
    sys.exit(main())
