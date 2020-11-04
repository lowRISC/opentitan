#!/usr/bin/env python3
# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

# Development helper: create
from Crypto.PublicKey import RSA
import sys

def print_array(varname: str, val: int, size_bytes: int):
    print("uint8_t %s[%d] = {%s};" % (varname, size_bytes, ', '.join(["0x%02x" % i for i in val.to_bytes(size_bytes, byteorder="little")])))

def main() -> int:
    if len(sys.argv) < 2:
        print("Usage: %s PRIVATE_KEY_PEM_FILE ['plaintext message']" % sys.argv[0])
        sys.exit(1)

    if len(sys.argv) >= 3:
        in_str = sys.argv[2]
    else:
        in_str = "Hello OTBN, can you encrypt and decrypt this for me?"

    private_key_file = sys.argv[1]
    in_bytes = in_str.encode("utf-8")
    print("Using private key {}, and plaintext message {!r}".format(private_key_file, in_bytes))
    print("")

    private_key = RSA.import_key(open(private_key_file).read())

    data = int.from_bytes(in_bytes, byteorder="little", signed=False)

    print("// modulus (n)")
    print_array("modulus", private_key.n, private_key.size_in_bytes())
    print("")

    print("// private exponent (d)")
    print_array("private_exponent", private_key.d, private_key.size_in_bytes())
    print("")

    print("// decrypted/plaintext message")
    print_array("in", data, private_key.size_in_bytes())
    print("")

    print("// encrypted message")
    encrypted = private_key._encrypt(data)
    print_array("encrypted_expected", encrypted, private_key.size_in_bytes())
    print("")

if __name__ == "__main__":
    sys.exit(main())
