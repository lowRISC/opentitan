#!/usr/bin/env python3

from string import Template
import argparse
import os.path
import sys
import binascii


parser = argparse.ArgumentParser(description='Convert binary file to verilog rom')
parser.add_argument('filename', metavar='filename', nargs=1,
                   help='filename of input binary')

args = parser.parse_args()
file = args.filename[0];

# check that file exists
if not os.path.isfile(file):
    print("File {} does not exist.".format(filename))
    sys.exit(1)

filename = os.path.splitext(file)[0]

license = """\
/* Copyright 2018 ETH Zurich and University of Bologna.
 * Copyright and related rights are licensed under the Solderpad Hardware
 * License, Version 0.51 (the "License"); you may not use this file except in
 * compliance with the License.  You may obtain a copy of the License at
 * http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
 * or agreed to in writing, software, hardware and materials distributed under
 * this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
 * CONDITIONS OF ANY KIND, either express or implied. See the License for the
 * specific language governing permissions and limitations under the License.
 *
 * File: $filename.v
 *
 * Description: Auto-generated bootrom
 */

// Auto-generated code
"""

module = """\
module $filename (
   input  logic         clk_i,
   input  logic         req_i,
   input  logic [63:0]  addr_i,
   output logic [63:0]  rdata_o
);
    localparam int RomSize = $size;

    const logic [RomSize-1:0][63:0] mem = {
$content
    };

    logic [$$clog2(RomSize)-1:0] addr_q;

    always_ff @(posedge clk_i) begin
        if (req_i) begin
            addr_q <= addr_i[$$clog2(RomSize)-1+3:3];
        end
    end

    // this prevents spurious Xes from propagating into
    // the speculative fetch stage of the core
    assign rdata_o = (addr_q < RomSize) ? mem[addr_q] : '0;
endmodule
"""

c_var = """\
// Auto-generated code

const int reset_vec_size = $size;

uint32_t reset_vec[reset_vec_size] = {
$content
};
"""

def read_bin():

    with open(filename + ".img", 'rb') as f:
        rom = binascii.hexlify(f.read())
        rom = map(''.join, zip(rom[::2], rom[1::2]))


    # align to 64 bit
    align = (int((len(rom) + 7) / 8 )) * 8;

    for i in range(len(rom), align):
        rom.append("00")

    return rom

rom = read_bin()

""" Generate C header file for simulator
"""
with open(filename + ".h", "w") as f:
    rom_str = ""
    # process in junks of 32 bit (4 byte)
    for i in range(0, int(len(rom)/4)):
        rom_str += "    0x" + "".join(rom[i*4:i*4+4][::-1]) + ",\n"

    # remove the trailing comma
    rom_str = rom_str[:-2]

    s = Template(c_var)
    f.write(s.substitute(filename=filename, size=int(len(rom)/4), content=rom_str))

    f.close()

""" Generate SystemVerilog bootcode for FPGA and ASIC
"""
with open(filename + ".sv", "w") as f:
    rom_str = ""
    # process in junks of 64 bit (8 byte)
    for i in reversed(range(int(len(rom)/8))):
        rom_str += "        64'h" + "".join(rom[i*8+4:i*8+8][::-1]) + "_" + "".join(rom[i*8:i*8+4][::-1]) + ",\n"

    # remove the trailing comma
    rom_str = rom_str[:-2]

    f.write(license)
    s = Template(module)
    f.write(s.substitute(filename=filename, size=int(len(rom)/8), content=rom_str))

