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

    # Pad with 0s, if not word-aligned
    byte_list += ["00"] * ((4 - len(byte_list)) % 4)

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

    # Following dict helps with translation to enum values from C.
    conversion_dict = {
        "SHA256": "Sha256",
        "SHA384": "Sha384",
        "SHA512": "Sha512",
        "HMAC256": "HmacSha256",
        "HMAC384": "HmacSha384",
        "HMAC512": "HmacSha512",
    }

    # Convert the message into an array of bytes
    for t in testvecs:
        if t["operation"] not in conversion_dict.keys():
            raise ValueError("Wrong operation defined in hjson testvector file.")
        t["test_operation"] = "kHmacTestOperation" + conversion_dict[t["operation"]]
        t["message"] = str_to_hex_array(t["input_msg"], return_byte_array=True)

        # Keys and digests are in 32b granularity
        t["digest"] = str_to_hex_array(t["digest"], return_byte_array=False)
        if t["operation"] in ["HMAC256", "HMAC384", "HMAC512"]:
            t["key_len"] = len(t["key"]) / 2 - 1
            t["key_mode"] = "kOtcryptoKeyMode" + conversion_dict[t["operation"]]
            t["keyblob"] = str_to_hex_array(t["key"], return_byte_array=False)
            t["keyblob"] += ["0x00000000"] * len(t["keyblob"])

    args.headerfile.write(Template(args.template.read()).render(tests=testvecs))
    args.headerfile.close()
    args.template.close()

    return 0


if __name__ == '__main__':
    sys.exit(main())
