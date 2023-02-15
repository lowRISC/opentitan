#!/bin/bash
# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

# Script to formally verify the masking of the OTBN using Alma.

echo "Verifying OTBN using Alma"

# Parse
python3 parse.py --keep --top-module otbn_top_coco --log-yosys \
  --source ${REPO_TOP}/hw/ip/otbn/pre_sca/alma/rtl/ram_1p.v \
  ${REPO_TOP}/hw/ip/otbn/pre_syn/syn_out/latest/generated/otbn_core.alma.v \
  ${REPO_TOP}/hw/ip/otbn/pre_sca/alma/rtl/otbn_top_coco.v

# Assemble the program
program=isw_and
cd examples/otbn || exit
python3 assemble.py --program programs/${program}.S \
  --netlist ../../tmp/circuit.v
cd ../../ || exit

# Trace
python3 trace.py --testbench tmp/verilator_tb.c \
  --netlist tmp/circuit.v \
  --c-compiler gcc \
  --make-jobs 16

# Generate bignum register file labels
examples/otbn/labels/generate_bignum_rf_labels.py \
  -i examples/otbn/labels/${program}_labels.txt \
  -o tmp/labels_updated.txt -w 1 -s 0

# Verify
python3 verify.py --json tmp/circuit.json \
  --top-module otbn_top_coco \
  --label tmp/labels_updated.txt \
  --vcd tmp/circuit.vcd \
  --checking-mode per-location \
  --rst-name rst_sys_n \
  --rst-phase 0 \
  --rst-cycles 2 \
  --init-delay 139 \
  --cycles 25 \
  --excluded-signals u_otbn_core.u_otbn_controller.rf_bignum_intg_err_i[0] \
  --glitch-behavior loose \
  --dbg-signals otbn_cycle_cnt_o \
  --mode stable
