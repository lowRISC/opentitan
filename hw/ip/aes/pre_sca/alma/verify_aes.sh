#!/bin/bash
# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

# Script to formally verify the masking of the AES unit using Alma.

set -e

# Argument parsing
if [[ "$#" -gt 0 ]]; then
  TOP_MODULE=$1
else
  TOP_MODULE=aes_sbox
fi

# aes_sub_bytes and aes_reduced_round share the same testbench.
if [[ ${TOP_MODULE} == "aes_sbox" ]]; then
  TESTBENCH=${TOP_MODULE}
elif  [[ ${TOP_MODULE} == "aes_sub_bytes" || ${TOP_MODULE} == "aes_reduced_round" ]]; then
  TESTBENCH="aes_sub_bytes"
else
  echo "TOP_MODULE ${TOP_MODULE} not supported, aborting now"
  exit 1
fi

echo "Verifying ${TOP_MODULE} using Alma"

# Parse
./parse.py --top-module ${TOP_MODULE} \
--source ${REPO_TOP}/hw/ip/aes/pre_syn/syn_out/latest/generated/${TOP_MODULE}.alma.v \
--netlist tmp/circuit.v --log-yosys

# Label
sed -i 's/\(data_i\s\[\)\([0-9]\+:0\)\(\]\s=\s\)unimportant/\1\2\3secret \2/g' tmp/labels.txt
sed -i 's/\(mask_i\s\[\)\([0-9]\+:0\)\(\]\s=\s\)unimportant/\1\2\3secret \2/g' tmp/labels.txt
sed -i 's/\(prd_i\s\[[0-9]\+:0\]\s=\s\)unimportant/\1random/g' tmp/labels.txt

# Trace
./trace.py --testbench ${REPO_TOP}/hw/ip/aes/pre_sca/alma/cpp/verilator_tb_${TESTBENCH}.cpp \
--netlist tmp/circuit.v -o tmp/circuit

# Verify
./verify.py --json tmp/circuit.json \
   --label tmp/labels.txt \
   --top-module ${TOP_MODULE} \
   --vcd tmp/tmp.vcd \
   --rst-name rst_ni --rst-phase 0 \
   --probe-duration once --mode transient \
   --glitch-behavior loose --cycles 6
