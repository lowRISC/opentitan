# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

from Crypto.Hash import cSHAKE128

TOKEN_LEN = 16
TOKEN_PREIMAGE = b'\x11\x11\x11\x11\x11\x11\x11\x11\x11\x11\x11\x11\x11\x11\x11\x11'

if __name__ == '__main__':
    hash_obj = cSHAKE128.new(data=TOKEN_PREIMAGE, custom=b'LC_CTRL')
    digest_bytes = hash_obj.read(TOKEN_LEN)
    digest_int = int.from_bytes(digest_bytes, byteorder='little')

    preimage_literal = '[' + ','.join(hex(byte)
                                      for byte in TOKEN_PREIMAGE) + ']'
    literal = f'0x{digest_int:032x}'
    print(f'preimage literal: {preimage_literal}')
    print(f'postimage literal: {literal}')
