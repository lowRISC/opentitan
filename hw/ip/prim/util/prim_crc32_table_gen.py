#!/usr/bin/env python3
# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

import binascii

function_header = '''
// Generated using hw/ip/prim/util/prim_crc32_table_gen.py
function automatic logic [31:0] crc32_byte_calc(logic [7:0] b);
  unique case (b)'''

function_footer = '''    default: crc32_byte_calc = '0;
  endcase
endfunction
'''

function_table_line = "    8'h{:02x}:   crc32_byte_calc = 32'h{:08x};"


def main():
    print(function_header)
    # Loop through all bytes to calculate a lookup table.
    for i in range(256):
        # The CRC update function using a byte lookup table is:
        #
        # crc = (crc >> 8) ^ crc_table[(crc & 0xff) ^ b]
        #
        # Where b is the byte input and the initial CRC is 0xffffffff. So given
        # input i, an inverted i (i ^ 0xff) is the input to the table giving
        # `table_in`.  binascii.crc32 inverts the crc before returning. The ^
        # 0xff000000 reverses this along with the (crc >> 8) that is XORed to
        # the table output giving table_out.
        table_in = i ^ 0xff
        b = i.to_bytes(1, byteorder='little')
        table_out = binascii.crc32(b) ^ 0xff000000
        print(function_table_line.format(table_in, table_out))
    print(function_footer)


if __name__ == '__main__':
    main()
