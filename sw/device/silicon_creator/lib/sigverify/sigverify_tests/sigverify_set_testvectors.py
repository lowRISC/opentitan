#!/usr/bin/env python3
# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

import argparse
import sys

import hjson
from Crypto.Hash import SHA256
from mako.template import Template

'''
Read in a JSON test vector file, convert the test vector to C constants, and
generate a header file with these test vectors.
'''

# Number of 32-bit words in a 3072-bit number
RSA_3072_NUMWORDS = int(3072 / 32)

# Number of 32-bit words in a 256-bit number
INT_256_NUMWORDS = int(256 / 32)


def compute_n0_inv(n):
    '''Compute -(n^-1) mod 2^256, a Montgomery constant.

    Sigverify expects this constant to be precomputed.
    '''
    # Note: On Python 3.8 and above, this could simply be: pow(-n, -1, 2**256).
    # Unfortunately, older versions of Python 3 don't support negative modular
    # exponents, so we use the standard algorithm from "Montgomery Arithmetic
    # from a Software Perspective" (https://eprint.iacr.org/2017/1057)
    # (algorithm 3).
    w = 256
    y = 1
    # n0 = n mod 2^256
    n0 = n & ((1 << 256) - 1)
    # maski = 2^i - 1 (start with i=2)
    maski = 3
    for i in range(2, w + 1):
        # (n * y) mod 2^i = (n0 * y) mod 2^i because i <= 256
        if (n0 * y) & maski != 1:
            y = y + (1 << (i - 1))
        maski <<= 1
        maski += 1
    return (1 << w) - y


def encode_message(msg_bytes):
    '''Get the message encoded according to PKCS v1.5.

    Returns the encoded message as big-endian bytes.

    Encodes the message according to RFC 8017, section 9.2, with a SHA2-256
    hash function. See
    https://datatracker.ietf.org/doc/html/rfc8017#section-9.2
    '''
    digest = SHA256.new(msg_bytes).digest()

    # T is the DER encoding of the digest
    sha256_prefix = b'\x30\x31\x30\x0d\x06\x09\x60\x86\x48\x01\x65\x03\x04\x02\x01\x05\x00\x04\x20'
    T = sha256_prefix + digest

    # Encoding is 0x00 || 0x01 || PS || 0x00 || T
    # Encoded message should be 3072 / 8 = 384 bytes
    PS_length = 384 - len(T) - 3
    PS = b'\xff' * PS_length

    # Final encoded message
    em = b'\x00\x01' + PS + b'\x00' + T
    assert len(em) == 384

    return em


def rsa_3072_int_to_hexwords(x):
    '''Convert a 3072-bit integer to a list of 32-bit integers (little-endian).'''
    out = []
    for _ in range(RSA_3072_NUMWORDS):
        out.append(x & ((1 << 32) - 1))
        x >>= 32
    # Note: some test sets may contain (invalid) signatures that are > 3072
    # words. The type signature of our RSA-3072 implementation rules out
    # getting the full value as input, so they are truncated here.
    return [f'{w:#010x}' for w in out]


def int_256_to_hexwords(x):
    '''Convert a 256-bit integer to a list of 32-bit integers (little-endian).'''
    out = []
    for _ in range(INT_256_NUMWORDS):
        out.append(x & ((1 << 32) - 1))
        x >>= 32
    if (x != 0):
        raise RuntimeError('Excess bits in 256-bit integer: {:#x}'.format(x))
    return ['{:#010x}'.format(w) for w in out]


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

    # Exclude test vectors with invalid exponents.
    testvecs = [t for t in testvecs if t['e'] == 65537]

    # Convert the 3072-bit numbers n and sig into words expressed in hex
    for t in testvecs:
        t['n_hexwords'] = rsa_3072_int_to_hexwords(t['n'])
        t['sig_hexwords'] = rsa_3072_int_to_hexwords(t['signature'])
        n0_inv = compute_n0_inv(t['n'])
        t['n0_inv_hexwords'] = int_256_to_hexwords(n0_inv)

    # Compute the SHA-256 digest of the message
    for t in testvecs:
        msg_bytes = t['msg'].to_bytes(t['msg_len'], byteorder='big')
        encoded = int.from_bytes(encode_message(msg_bytes), byteorder='big')
        t['encoded_msg_hexwords'] = rsa_3072_int_to_hexwords(encoded)

    args.headerfile.write(Template(args.template.read()).render(tests=testvecs))
    args.headerfile.close()
    args.template.close()

    return 0


if __name__ == '__main__':
    sys.exit(main())
