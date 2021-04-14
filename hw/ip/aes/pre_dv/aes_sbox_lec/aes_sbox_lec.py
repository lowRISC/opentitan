#!/usr/bin/env python3
# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
r"""Command-line tool to perform LEC on all AES S-Box implementations using Yosys

"""
import glob
import os
import subprocess
import sys
from pathlib import Path


def replace_module_name(file_name, string_search, string_replace):
    fin = open(file_name, 'rt')
    data = fin.read()
    data = data.replace(string_search, string_replace)
    fin.close()
    fin = open(file_name, 'wt')
    fin.write(data)
    fin.close()


path_root = str(Path(__file__).resolve().parents[5])
rtl_path = path_root + '/hw/ip/aes/rtl/'
prim_path = path_root + '/hw/ip/prim/rtl/'
prim_xilinx_path = path_root + '/hw/ip/prim_xilinx/rtl/'

# Specify S-Box reference implementation
impl_gold = 'aes_sbox_lut'
file_pkg = 'aes_pkg.sv'

# Specify dependencies
dep_list = [
    rtl_path + 'aes_pkg.sv',
    rtl_path + 'aes_reg_pkg.sv',
    rtl_path + 'aes_sbox_canright_pkg.sv',
    prim_xilinx_path + 'prim_xilinx_buf.sv',
    prim_xilinx_path + 'prim_xilinx_xor2.sv',
]

# Detect all S-Box implementations to check
impl_list = glob.glob(rtl_path + 'aes_sbox_*.sv')
impl_list = [
    impl_dut.replace(rtl_path, '').replace('.sv', '') for impl_dut in impl_list
]
# Remove multicycle implementations, we can't perform LEC for those.
impl_list.remove('aes_sbox_dom')
# Remove reference implementation and package files.
impl_list.remove(impl_gold)
impl_list.remove('aes_sbox_canright_pkg')

# Create workdir
os.makedirs('scratch', exist_ok=True)

# Convert the reference implementation to Verilog
sv2v_cmd = ['sv2v', '-I', prim_path
            ] + dep_list + [rtl_path + impl_gold + '.sv']
with open('scratch/aes_sbox_ref.v', 'w') as outfile:
    subprocess.run(sv2v_cmd, stdout=outfile)

# Change module name
replace_module_name('scratch/aes_sbox_ref.v', impl_gold, 'aes_sbox_ref')

print('Running LEC on ' + str(len(impl_list)) + ' S-Box implementation(s)...')

# Check every implementation separately
num_impl_success = 0
num_impl_failed = 0
for impl_dut in impl_list:

    # Prepare Verilog conversion of DUT
    sv2v_cmd = ['sv2v', '-I', prim_path
                ] + dep_list + [rtl_path + impl_dut + '.sv']

    # Masked implementations require a wrapper
    if 'masked' in impl_dut:
        file_wrap = 'aes_sbox_masked_wrapper.sv'

        # Copy the wrapper
        os.system('cp ' + file_wrap + ' scratch/' + file_wrap)

        # Change module name
        replace_module_name('scratch/' + file_wrap, 'aes_sbox_masked',
                            impl_dut)

        # Include in conversion
        sv2v_cmd.insert(3, 'scratch/' + file_wrap)

    # Convert DUT to Verilog
    with open('scratch/aes_sbox_dut.v', 'w') as outfile:
        subprocess.run(sv2v_cmd, stdout=outfile)

    # Change module name
    if 'masked' in impl_dut:
        replace_module_name('scratch/aes_sbox_dut.v', impl_dut + '_wrapper',
                            'aes_sbox_dut')
    else:
        replace_module_name('scratch/aes_sbox_dut.v', impl_dut, 'aes_sbox_dut')

    # Use Xilinx implementation for primitives
    replace_module_name('scratch/aes_sbox_dut.v', 'prim_xilinx_', 'prim_')

    # Perform LEC in Yosys
    yosys_cmd = ['yosys', '../aes_sbox_lec.ys']
    lec_log = 'scratch/' + impl_dut + '_lec.log'
    with open(lec_log, 'w') as outfile:
        subprocess.run(yosys_cmd, cwd="scratch", stdout=outfile)

    # Get actual LEC output
    lec_string = 'Trying to prove $equiv'
    lec_lines = []
    with open(lec_log, 'rt') as fin:
        data = fin.read()
        for line in data.split('\n'):
            if lec_string in line:
                lec_lines.append(line)

    # Check for LEC output
    num_lec_success = 0
    num_lec_failed = 0
    for line in lec_lines:
        if 'success!' in line:
            num_lec_success = num_lec_success + 1
        if 'failed.' in line:
            num_lec_failed = num_lec_failed + 1

    if (len(lec_lines) == 0) or (len(lec_lines) !=
                                 num_lec_success) or (num_lec_failed > 0):
        print("LEC failed: \t\t\t" + impl_dut + '.sv\n-> ' + 'Check ' +
              lec_log + ' for details.')
        num_impl_failed = num_impl_failed + 1
    else:
        print("LEC completed successfully: \t" + impl_dut + '.sv')
        num_impl_success = num_impl_success + 1

# Print output
print('Done.')
if (num_impl_success == len(impl_list)) and not num_impl_failed:
    print('SUCCESS!')
else:
    print('FAILED for ' + str(num_impl_failed) + ' implementation(s).')
    sys.exit(1)
