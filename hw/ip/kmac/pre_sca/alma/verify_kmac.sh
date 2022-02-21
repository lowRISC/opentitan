#!/bin/bash
# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

# Script to formally verify the masking of KMAC using Alma.

set -e

# Argument parsing
if [[ "$#" -gt 0 ]]; then
  TOP_MODULE=$1
else
  TOP_MODULE=keccak_2share
fi

# Select testbench.
if [[ ${TOP_MODULE} == "keccak_2share" ]]; then
  TESTBENCH=${TOP_MODULE}
else
  echo "TOP_MODULE ${TOP_MODULE} not supported, aborting now"
  exit 1
fi

echo "Verifying ${TOP_MODULE} using Alma"

## Parse
./parse.py --top-module ${TOP_MODULE} \
--source ${REPO_TOP}/hw/ip/kmac/pre_syn/syn_out/latest/generated/${TOP_MODULE}.alma.v \
--netlist tmp/circuit.v --log-yosys

# Label
# Extract WIDTH from label file.
WIDTH_DOUBLE_MIN_1=`cat tmp/labels.txt | grep s_i | sed 's/^[^0-9]*\([0-9]\+\).*/\1/'`
WIDTH_DOUBLE=$((WIDTH_DOUBLE_MIN_1 + 1))
WIDTH=$((WIDTH_DOUBLE / 2))
WIDTH_MIN_1=$((WIDTH - 1))
# Modify label template
# Change rand_i
sed -i 's/\(rand_i\s\[[0-9]\+:0\]\s=\s\)unimportant/\1random/g' tmp/labels.txt
# Generate s_i string
S_I=$"s_i [$WIDTH_MIN_1:0] = secret $WIDTH_MIN_1:0\ns_i [$((WIDTH*2-1)):$WIDTH] = secret $WIDTH_MIN_1:0"
# Replace s_i by new string
sed -i "s/\(s_i\s\[\)\([0-9]\+:0\)\(\]\s=\s\)unimportant/${S_I}/g" tmp/labels.txt

# Trace
./trace.py --testbench ${REPO_TOP}/hw/ip/kmac/pre_sca/alma/cpp/verilator_tb_${TESTBENCH}.cpp \
--netlist tmp/circuit.v -o tmp/circuit

# Verify
./verify.py --json tmp/circuit.json \
   --label tmp/labels.txt \
   --top-module ${TOP_MODULE} \
   --vcd tmp/tmp.vcd \
   --rst-name rst_ni --rst-phase 0 \
   --probe-duration once --mode transient \
   --glitch-behavior loose --cycles 8
