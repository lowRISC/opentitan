#!/bin/bash
# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

# Script to formally verify the masking of the AES unit using Alma.

set -e

export TOP_MODULE=aes_sbox

echo "Verifying ${TOP_MODULE} using Alma"

# Parse
./parse.py --top-module ${TOP_MODULE} \
--source ${REPO_TOP}/hw/ip/aes/pre_syn/syn_out/latest/generated/${TOP_MODULE}.pre_map.v \
--netlist tmp/circuit.v --log-yosys

# Trace
./trace.py --testbench ${REPO_TOP}/hw/ip/aes/pre_sca/alma/cpp/verilator_tb_${TOP_MODULE}.cpp \
--netlist tmp/circuit.v -o tmp/circuit

# Verify
./verify.py --json tmp/circuit.json \
   --label ${REPO_TOP}/hw/ip/aes/pre_sca/alma/labels/${TOP_MODULE}.txt \
   --top-module ${TOP_MODULE} \
   --vcd tmp/tmp.vcd \
   --rst-name rst_ni --rst-phase 0 \
   --probe-duration once --mode transient \
   --glitch-behavior loose --cycles 6
