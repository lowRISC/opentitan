#!/bin/bash
# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

# Script to formally verify the masking of the GHASH block for AES-GCM using Alma.

set -e

# Argument parsing
TOP_MODULE=aes_ghash_wrap
TESTBENCH=${TOP_MODULE}

echo "Verifying ${TOP_MODULE} using Alma"

# Parse
./parse.py --top-module ${TOP_MODULE} \
--source ${REPO_TOP}/hw/ip/aes/pre_syn/syn_out/latest/generated/${TOP_MODULE}.alma.v \
--netlist tmp/circuit.v --log-yosys

# Label
# Change rand_i
sed -i 's/\(prd_i\s\[[0-9]\+:0\]\s=\s\)unimportant/\1random/g' tmp/labels.txt
# Secrets
WIDTH=128
WIDTH_MIN_1=$((WIDTH - 1))
WIDTH_X2=$((WIDTH*2))
WIDTH_X2_MIN_1=$((WIDTH_X2 - 1))

# Generate hash_subkey_i string
HASH_SUBKEY_I=$"hash_subkey_i [$WIDTH_MIN_1:0] = secret $WIDTH_MIN_1:0\nhash_subkey_i [$((WIDTH*2-1)):$WIDTH] = secret $WIDTH_MIN_1:0"
# Generate s_i string
S_I=$"s_i [$WIDTH_MIN_1:0] = secret $WIDTH_X2_MIN_1:$WIDTH\ns_i [$((WIDTH*2-1)):$WIDTH] = secret $WIDTH_X2_MIN_1:$WIDTH"
# Replace strings
sed -i "s/\(hash_subkey_i\s\[\)\([0-9]\+:0\)\(\]\s=\s\)unimportant/${HASH_SUBKEY_I}/g" tmp/labels.txt
sed -i "s/^\(s_i\s\[\)\([0-9]\+:0\)\(\]\s=\s\)unimportant/${S_I}/g" tmp/labels.txt

# Trace
./trace.py --testbench ${REPO_TOP}/hw/ip/aes/pre_sca/alma/cpp/verilator_tb_${TESTBENCH}.cpp \
  --netlist tmp/circuit.v --c-compiler gcc -o tmp/circuit

# Verify
./verify.py --json tmp/circuit.json \
  --label tmp/labels.txt \
  --top-module ${TOP_MODULE} \
  --vcd tmp/tmp.vcd \
  --rst-name rst_ni --rst-phase 0 \
  --probe-duration once \
  --mode transient \
  --glitch-behavior loose \
  --cycles 37
