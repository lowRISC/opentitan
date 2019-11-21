#!/usr/bin/env python3
# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
"""HMAC-SHA256 Python implementation
"""

import argparse
import binascii
import hmac as hm
import hashlib  # for comparison
import logging as log
import sys
from array import array
from io import StringIO

import numpy as np

init_h = [
    0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a, 0x510e527f, 0x9b05688c,
    0x1f83d9ab, 0x5be0cd19
]

k = [
    0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1,
    0x923f82a4, 0xab1c5ed5, 0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3,
    0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174, 0xe49b69c1, 0xefbe4786,
    0x0fc19dc6, 0x240ca1cc, 0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
    0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7, 0xc6e00bf3, 0xd5a79147,
    0x06ca6351, 0x14292967, 0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13,
    0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85, 0xa2bfe8a1, 0xa81a664b,
    0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
    0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a,
    0x5b9cca4f, 0x682e6ff3, 0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208,
    0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2
]


def rotr(v: np.uint32, amt: int) -> np.uint32:
    return (v >> amt) | ((v << (32 - amt)) & 0xFFFFFFFF)


def shiftr(v: np.uint32, amt: int) -> np.uint32:
    return (v >> amt)


def sha256(msg: bin) -> bin:
    # Assume given message is always byte aligned
    L = len(bytes(msg)) * 8
    zero_padding_length = (512 - ((L + 8 + 64) % 512))
    log.info("0 padding: %d bits" % (zero_padding_length))
    # padding
    new_msg = msg + b'\x80' + (b'\0' * (
        (zero_padding_length // 8))) + L.to_bytes(
            8, byteorder='big')
    new_L = len(new_msg)

    log.info("Padded message: %s" % (binascii.b2a_hex(new_msg)))
    # Convert byte to 32bit array
    #w_array = np.array(new_msg, dtype=np.uint32)
    dt = np.dtype(np.uint32)
    dt = dt.newbyteorder('>')  # bigendian
    w_array = np.frombuffer(new_msg, dtype=dt)

    # compress function
    [h0, h1, h2, h3, h4, h5, h6, h7] = init_h
    for i in range(0, new_L // 4, 16):  # every 512 bit
        # create w
        # 16 entry x 32 bit word
        w = w_array[i:i + 16]
        #for j in range(16):

        [a, b, c, d, e, f, g, h] = [h0, h1, h2, h3, h4, h5, h6, h7]
        for i in range(64):
            w_entry = w[0]
            # Calculate 16th entry and push to the end
            #   s0 = (w[i-15] rotr 7) xor (w[i-15] rotr 18) xor (w[i-15] shiftr 3)
            #   s1 = (w[i-2] rotr 17) xor (w[i-2] rotr 19) xor (w[i-2] shiftr 10)
            #   w[i] = w[i-16] + s0 + w[i-7] + s1
            sum_0 = rotr(w[1], 7) ^ rotr(w[1], 18) ^ shiftr(w[1], 3)
            sum_1 = rotr(w[14], 17) ^ rotr(w[14], 19) ^ shiftr(w[14], 10)
            w = np.append(w[1:16], 0xFFFFFFFF & (w[0] + sum_0 + w[9] + sum_1))

            # Compress
            S1 = rotr(e, 6) ^ rotr(e, 11) ^ rotr(e, 25)
            ch = (e & f) ^ ((~e) & g)
            temp1 = (h + S1 + ch + k[i] + w_entry) & 0xFFFFFFFF
            S0 = rotr(a, 2) ^ rotr(a, 13) ^ rotr(a, 22)
            maj = (a & b) ^ (a & c) ^ (b & c)
            temp2 = (S0 + maj) & 0xFFFFFFFF

            h = g
            g = f
            f = e
            e = (d + temp1) & 0xFFFFFFFF
            d = c
            c = b
            b = a
            a = (temp1 + temp2) & 0xFFFFFFFF

        h0 = (h0 + a) & 0xFFFFFFFF
        h1 = (h1 + b) & 0xFFFFFFFF
        h2 = (h2 + c) & 0xFFFFFFFF
        h3 = (h3 + d) & 0xFFFFFFFF
        h4 = (h4 + e) & 0xFFFFFFFF
        h5 = (h5 + f) & 0xFFFFFFFF
        h6 = (h6 + g) & 0xFFFFFFFF
        h7 = (h7 + h) & 0xFFFFFFFF

    # merge
    digest = np.array([h0, h1, h2, h3, h4, h5, h6, h7], dtype=dt).tobytes()

    return digest


def _hmac(key: bin, src: bin, hashf) -> bin:
    blocksize = 64  # SHA-256
    if len(key) > blocksize:
        key = hashf(key)
    key = key + b'\00' * (blocksize - len(key))
    log.info("Padded Key: %s" % binascii.b2a_hex(key).decode('utf-8'))
    ipad = bytes([x ^ 0x36 for x in key])
    opad = bytes([x ^ 0x5c for x in key])
    meta_v = hashf(ipad + src)
    log.info("Meta hash output: %s" % binascii.b2a_hex(meta_v).decode('utf-8'))
    sig = hashf(opad + meta_v)
    return sig


def main():
    parser = argparse.ArgumentParser(prog="hmac")
    parser.add_argument(
        'message',
        nargs='?',
        metavar='file',
        type=argparse.FileType('rb'),
        default=sys.stdin,
        help="Message file.")
    parser.add_argument(
        '--big-endian',
        '-b',
        action='store_true',
        default=True,
        help='Input/Output are Big Endians')
    parser.add_argument(
        '--key', '-k', type=str, help='HMAC Secret Key in Big Endian')
    parser.add_argument('--verbose', '-v', action='store_true', help='Verbose')

    args = parser.parse_args()

    if args.verbose:
        log.basicConfig(format="%(levelname)s: %(message)s", level=log.DEBUG)
    else:
        log.basicConfig(format="%(levelname)s: %(message)s")

    log.info("Secret Key: %s" % args.key)

    # Convert key to binary
    try:
        key = bytes.fromhex(args.key)
    except ValueError:
        log.error("Key should be Hex format without '0x' prefix")
        raise SystemExit(sys.exec_info()[1])

    with args.message:
        try:
            src = args.message.read()
            if args.message == sys.stdin:
                # Converting to binary format
                src = src.strip().encode('utf-8')
            log.info("Message: %s" % src)
        except ValueError:
            raise SystemExit(sys.exec_info()[1])

    hashlib_out = hashlib.sha256(src)
    log.info("hashlib(BE): 0x%s" % hashlib_out.hexdigest())

    model_out = sha256(src)
    log.info("model  (BE): 0x%s" % binascii.b2a_hex(model_out).decode('utf-8'))

    if hashlib_out.hexdigest() != binascii.b2a_hex(model_out).decode('utf-8'):
        raise SystemExit("Miscompare")

    # HMAC
    hashlib_hmac = hm.new(key, src, hashlib.sha256)
    log.info("hmac:  %s" % hashlib_hmac.hexdigest())

    model_hmac = _hmac(key, src, sha256)
    log.info("model: %s" % binascii.b2a_hex(model_hmac).decode('utf-8'))

    if hashlib_hmac.hexdigest() != binascii.b2a_hex(model_hmac).decode(
            'utf-8'):
        raise SystemExit("HMAC Miscompare")


if __name__ == "__main__":
    main()
