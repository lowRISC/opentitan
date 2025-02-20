#!/usr/bin/env python3
# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
"""HMAC-SHA256 Python implementation"""

import argparse
import binascii
import hmac as hm
import hashlib  # for comparison
import logging as log
import sys

import numpy as np

init_h = [
    0x6A09E667,
    0xBB67AE85,
    0x3C6EF372,
    0xA54FF53A,
    0x510E527F,
    0x9B05688C,
    0x1F83D9AB,
    0x5BE0CD19,
]

k = [
    0x428A2F98,
    0x71374491,
    0xB5C0FBCF,
    0xE9B5DBA5,
    0x3956C25B,
    0x59F111F1,
    0x923F82A4,
    0xAB1C5ED5,
    0xD807AA98,
    0x12835B01,
    0x243185BE,
    0x550C7DC3,
    0x72BE5D74,
    0x80DEB1FE,
    0x9BDC06A7,
    0xC19BF174,
    0xE49B69C1,
    0xEFBE4786,
    0x0FC19DC6,
    0x240CA1CC,
    0x2DE92C6F,
    0x4A7484AA,
    0x5CB0A9DC,
    0x76F988DA,
    0x983E5152,
    0xA831C66D,
    0xB00327C8,
    0xBF597FC7,
    0xC6E00BF3,
    0xD5A79147,
    0x06CA6351,
    0x14292967,
    0x27B70A85,
    0x2E1B2138,
    0x4D2C6DFC,
    0x53380D13,
    0x650A7354,
    0x766A0ABB,
    0x81C2C92E,
    0x92722C85,
    0xA2BFE8A1,
    0xA81A664B,
    0xC24B8B70,
    0xC76C51A3,
    0xD192E819,
    0xD6990624,
    0xF40E3585,
    0x106AA070,
    0x19A4C116,
    0x1E376C08,
    0x2748774C,
    0x34B0BCB5,
    0x391C0CB3,
    0x4ED8AA4A,
    0x5B9CCA4F,
    0x682E6FF3,
    0x748F82EE,
    0x78A5636F,
    0x84C87814,
    0x8CC70208,
    0x90BEFFFA,
    0xA4506CEB,
    0xBEF9A3F7,
    0xC67178F2,
]


def rotr(v: np.uint32, amt: int) -> np.uint32:
    return (v >> amt) | ((v << (32 - amt)) & 0xFFFFFFFF)


def shiftr(v: np.uint32, amt: int) -> np.uint32:
    return v >> amt


def sha256(msg: bin) -> bin:
    # Assume given message is always byte aligned
    L = len(bytes(msg)) * 8
    zero_padding_length = 512 - ((L + 8 + 64) % 512)
    log.info("0 padding: %d bits" % (zero_padding_length))
    # padding
    new_msg = msg + b"\x80" + (b"\0" * (zero_padding_length // 8)) + L.to_bytes(8, byteorder="big")
    new_L = len(new_msg)

    log.info("Padded message: %s" % (binascii.b2a_hex(new_msg)))
    # Convert byte to 32bit array
    # w_array = np.array(new_msg, dtype=np.uint32)
    dt = np.dtype(np.uint32)
    dt = dt.newbyteorder(">")  # bigendian
    w_array = np.frombuffer(new_msg, dtype=dt)

    # compress function
    [h0, h1, h2, h3, h4, h5, h6, h7] = init_h
    for i in range(0, new_L // 4, 16):  # every 512 bit
        # create w
        # 16 entry x 32 bit word
        w = w_array[i : i + 16]
        # for j in range(16):

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
    key = key + b"\00" * (blocksize - len(key))
    log.info("Padded Key: %s" % binascii.b2a_hex(key).decode("utf-8"))
    ipad = bytes([x ^ 0x36 for x in key])
    opad = bytes([x ^ 0x5C for x in key])
    meta_v = hashf(ipad + src)
    log.info("Meta hash output: %s" % binascii.b2a_hex(meta_v).decode("utf-8"))
    sig = hashf(opad + meta_v)
    return sig


def main():
    parser = argparse.ArgumentParser(prog="hmac")
    parser.add_argument(
        "message",
        nargs="?",
        metavar="file",
        type=argparse.FileType("rb"),
        default=sys.stdin,
        help="Message file.",
    )
    parser.add_argument(
        "--big-endian", "-b", action="store_true", default=True, help="Input/Output are Big Endians"
    )
    parser.add_argument("--key", "-k", type=str, help="HMAC Secret Key in Big Endian")
    parser.add_argument("--verbose", "-v", action="store_true", help="Verbose")

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
                src = src.strip().encode("utf-8")
            log.info("Message: %s" % src)
        except ValueError:
            raise SystemExit(sys.exec_info()[1])

    hashlib_out = hashlib.sha256(src)
    log.info("hashlib(BE): 0x%s" % hashlib_out.hexdigest())

    model_out = sha256(src)
    log.info("model  (BE): 0x%s" % binascii.b2a_hex(model_out).decode("utf-8"))

    if hashlib_out.hexdigest() != binascii.b2a_hex(model_out).decode("utf-8"):
        raise SystemExit("Miscompare")

    # HMAC
    hashlib_hmac = hm.new(key, src, hashlib.sha256)
    log.info("hmac:  %s" % hashlib_hmac.hexdigest())

    model_hmac = _hmac(key, src, sha256)
    log.info("model: %s" % binascii.b2a_hex(model_hmac).decode("utf-8"))

    if hashlib_hmac.hexdigest() != binascii.b2a_hex(model_hmac).decode("utf-8"):
        raise SystemExit("HMAC Miscompare")


if __name__ == "__main__":
    main()
