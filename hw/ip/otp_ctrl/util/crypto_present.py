# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

# default key size 128 bits, input data 64 bits
from ctypes import c_uint64, c_uint8, CDLL

# TODO: once we generate the crypto_present.so on the fly, might have to change
# this path
LIB_PATH = "../../prim/dv/prim_present/crypto_dpi_present/crypto_present.so"
NUM_ROUND = 31


def load_present_c_lib():
    '''Load crypto_present.so library and cast input and output with ctypes'''
    try:
        present_lib = CDLL(LIB_PATH)
    except Exception as e:
        print(e, ':could not recogized lib path: ', LIB_PATH)

    present_lib.c_encrypt.restype = c_uint64
    present_lib.c_encrypt.argtypes = (c_uint64, c_uint64, c_uint64, c_uint8, c_uint8)
    present_lib.c_decrypt.restype = c_uint64
    present_lib.c_decrypt.argtypes = (c_uint64, c_uint64, c_uint64, c_uint8, c_uint8)

    return present_lib


def get_keys(key):
    '''Separate keys to upper 64 bits and lower 64 bits'''
    return key >> 64, key % (1 << 64)


def present_encrypt(plaintext, key):
    ''' 31 round  PRESENT encryption algorithm

    Argument is 64 bits plaintext and 128 bits key.
    Returned output is 64 bits in hex format.

    '''

    present_lib = load_present_c_lib()
    key_high, key_low = get_keys(key)
    encrypted_value = present_lib.c_encrypt(c_uint64(plaintext),
                                            c_uint64(key_high),
                                            c_uint64(key_low),
                                            c_uint8(NUM_ROUND + 1),
                                            c_uint8(0))
    return hex(encrypted_value)


def present_decrypt(ciphertext, key):
    ''' 31 round  PRESENT decryption algorithm

    Argument is 64 bits ciphertext and 128 bits key.
    Returned output is 64 bits in hex format.

    '''

    present_lib = load_present_c_lib()
    key_high, key_low = get_keys(key)
    decrypted_value = present_lib.c_decrypt(c_uint64(ciphertext),
                                            c_uint64(key_high),
                                            c_uint64(key_low),
                                            c_uint8(NUM_ROUND + 1),
                                            c_uint8(0))
    return hex(decrypted_value)
