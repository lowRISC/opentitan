#!/usr/bin/env bash
# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

# Script to formally verify the masking of the mask accelerator using CocoAlma.

set -e

# Ensure the CocoAlma virtualenv's packages are found regardless of PYTHONPATH
# overrides from the calling environment (e.g. nix develop).
ALMA_SITE_PACKAGES="${HOME}/alma/dev/lib/python3.10/site-packages"
export PYTHONPATH="${ALMA_SITE_PACKAGES}${PYTHONPATH:+:${PYTHONPATH}}"

# Argument parsing
TARGET_TYPE="${1:-sec_add_mod}"
CYCLES=25
case "$TARGET_TYPE" in
  hpc2)        TOP_MODULE=prim_hpc2_sca_wrapper ;;
  hpc2o)       TOP_MODULE=prim_hpc2o_sca_wrapper ;;
  hpc3)        TOP_MODULE=prim_hpc3_sca_wrapper ;;
  hpc3o)       TOP_MODULE=prim_hpc3o_sca_wrapper ;;
  sec_add)     TOP_MODULE=otbn_mask_accelerator_sca_wrapper; CYCLES=17 ;;
  sec_add_mod) TOP_MODULE=otbn_mask_accelerator_sca_wrapper ;;
  a2b)         TOP_MODULE=otbn_mask_accelerator_sca_wrapper ;;
  b2a)         TOP_MODULE=otbn_mask_accelerator_sca_wrapper ;;
  *)           TOP_MODULE=otbn_mask_accelerator_sca_wrapper ;;
esac

case "$TARGET_TYPE" in
  hpc2 | hpc2o | hpc3 | hpc3o) TESTBENCH="${TOP_MODULE}" ;;
  *)                           TESTBENCH="${TOP_MODULE}_${TARGET_TYPE}" ;;
esac
export TOP_MODULE

echo "Verifying ${TOP_MODULE} using CocoAlma"

# Pre-process alma.v: shorten escaped identifiers whose C++ length exceeds
# VERILATOR_LIMIT - 11.  The 11-char reserve accounts for the longest port
# suffix that parse.py's internal flatten appends to kept prim_* instance names
# ('.out_o_n' from prim_xnor2: 4 cpp-chars for the dot + 7 chars = 11).
ALMA_V="${REPO_TOP}/hw/ip/otbn/pre_syn/syn_out/latest/generated/${TOP_MODULE}.alma.v"
ALMA_FLAT="${REPO_TOP}/hw/ip/otbn/pre_syn/syn_out/latest/generated/${TOP_MODULE}.alma.flat.v"
cp "${ALMA_V}" "${ALMA_FLAT}"
python3 ${REPO_TOP}/hw/ip/otbn/pre_sca/alma/shorten_alma_identifiers.py --reserve 11 "${ALMA_FLAT}"

# Parse
./parse.py --top-module ${TOP_MODULE} \
--source "${ALMA_FLAT}" \
--netlist tmp/circuit.v

# Label
sed -i 's/\(share0_i\s\[\)\([0-9]\+:0\)\(\]\s=\s\)unimportant/\1\2\3secret \2/g' tmp/labels.txt
sed -i 's/\(share1_i\s\[\)\([0-9]\+:0\)\(\]\s=\s\)unimportant/\1\2\3secret \2/g' tmp/labels.txt
sed -i 's/\(rand_i\(\s\[[0-9]\+:0\]\)\?\s=\s\)unimportant/\1random/g' tmp/labels.txt

# Trace
./trace.py --testbench ${REPO_TOP}/hw/ip/otbn/pre_sca/alma/cpp/verilator_tb_${TESTBENCH}.cpp \
  --netlist tmp/circuit.v --c-compiler gcc -o tmp/circuit

# Verify
# --cycles should be larger than the number of cycles to be evaluated.
./verify.py --json tmp/circuit.json \
  --label tmp/labels.txt \
  --top-module ${TOP_MODULE} \
  --vcd tmp/tmp.vcd \
  --rst-name rst_ni --rst-phase 0 \
  --probe-duration once \
  --mode transient \
  --glitch-behavior strict \
  --cycles ${CYCLES}
