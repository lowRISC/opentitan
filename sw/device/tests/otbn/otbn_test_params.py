#!/usr/bin/env python3
# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

""" Generate parameters for the OTBN end-to-end tests.
"""

from Crypto.PublicKey import RSA, ECC
import argparse
import sys
import secrets

C_DATATYPE = "static const uint8_t"

def print_array(varname: str, val: int, size_bytes: int):
    print("%s %s[%d] = {%s};" % (C_DATATYPE, varname, size_bytes, ', '.join(["0x%02x" % i for i in int(val).to_bytes(size_bytes, byteorder="little")])))

def print_string(varname: str, val: str, size_bytes: int):
    print("%s %s[%d] = {\"%s\"};" % (C_DATATYPE, varname, size_bytes, val))

def print_rsa_params(private_key_file: str, in_str: str) -> None:
    in_bytes = in_str.encode("utf-8")
    print("Using private key {}, and plaintext message {!r}".format(private_key_file, in_bytes))
    print("")

    private_key = RSA.import_key(open(private_key_file).read())

    data = int.from_bytes(in_bytes, byteorder="little", signed=False)

    print("// modulus (n)")
    print_array("kModulus", private_key.n, private_key.size_in_bytes())
    print("")

    print("// private exponent (d)")
    print_array("kPrivateExponent", private_key.d, private_key.size_in_bytes())
    print("")

    print("// decrypted/plaintext message")
    print_string("kIn", in_str, private_key.size_in_bytes())
    print("")

    print("// encrypted message")
    encrypted = private_key._encrypt(data)
    print_array("kEncryptedExpected", encrypted, private_key.size_in_bytes())
    print("")

def print_ecc_params(private_key_file: str, in_str: str) -> None:
    in_bytes = in_str.encode("utf-8")
    print("Using private key {}, and plaintext message {!r}".format(private_key_file, in_bytes))
    print("")

    key = ECC.import_key(open(private_key_file).read())
    assert key.has_private()
    key_size_bytes = key.public_key().pointQ.size_in_bytes()

    data = int.from_bytes(in_bytes, byteorder="little", signed=False)
    k = int.from_bytes(secrets.token_bytes(key_size_bytes), byteorder="little", signed=False)

    # Sign the input data
    (r, s) = key._sign(data, k)

    print("// Parameters for ECC {}".format(key.curve))

    print("// Message")
    print_string("kIn", in_str, key_size_bytes)
    print("")

    print("// Public key x-coordinate (Q.x)")
    print_array("kPublicKeyQx", key.public_key().pointQ.x, key_size_bytes)
    print("")

    print("// Public key y-coordinate (Q.y)")
    print_array("kPublicKeyQy", key.public_key().pointQ.y, key_size_bytes)
    print("")

    print("// Private key (d)")
    print_array("kPrivateKeyD", key.d, key_size_bytes)
    print("")

    print("// Secret random integer (k)")
    print_array("kSecretRandomIntK", k, key_size_bytes)
    print("")

    print("// Signature component r")
    print_array("kExpectedSignatureR", r, key_size_bytes)
    print("")

    print("// Signature component s")
    print_array("kExpectedSignatureS", s, key_size_bytes)
    print("")


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument('type', choices=('rsa', 'ecc'))
    parser.add_argument('private_key_pem_file')
    parser.add_argument('message', nargs='?', default="Hello OTBN.")

    args = parser.parse_args()

    if args.type == 'rsa':
        print_rsa_params(args.private_key_pem_file, args.message)
    elif args.type == 'ecc':
        print_ecc_params(args.private_key_pem_file, args.message)
    else:
        raise ValueError("Unknown type {!r}".format(args.type))

if __name__ == "__main__":
    sys.exit(main())
