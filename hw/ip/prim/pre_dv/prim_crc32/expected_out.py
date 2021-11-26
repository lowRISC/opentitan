# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

# Generates expected outputs for simple prim_crc32 testbench

import binascii

test_data = 0xdeadbeef
crc = 0x0
for i in range(2, 100):
    print(f'{crc:08x}')
    test_data_bytes = test_data.to_bytes(4, byteorder='little')
    crc = binascii.crc32(test_data_bytes, crc)
    test_count_bytes = i.to_bytes(1, byteorder='little')
    crc = binascii.crc32(test_count_bytes, crc)
    crc = binascii.crc32(test_count_bytes, crc)
    test_data += 1
