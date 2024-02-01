#!/bin/bash
# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

# Script to formally verify the masking of the post-synthesis AES S-box netlist with CocoAlma.

set -e

# If the output dir exists, remove files from previous run. Otherwise, create the folder.
if [ -d ${OUTPUT_DIR} ]; then
  rm -f ${OUTPUT_DIR}/circuit*
  rm -f ${OUTPUT_DIR}/labels.txt
  rm -f ${OUTPUT_DIR}/tmp.vcd
else
  echo "Creating ${OUTPUT_DIR}"
  mkdir -p ${OUTPUT_DIR}
fi

# Create an ad hoc techlib .v file by patching complex cells from given patch file.
# The following scripts reads the required filenames from environment variables, therefore we
# are not passing them as arguments.
echo "Patching up library cells"
${REPO_TOP}/hw/ip/aes/pre_sca/alma_post_syn/simplify_techlib.py

# `TOP_MDOULE` and `TESTBENCH` parameters are loaded as environment variables.
echo "Verifying post-synthesis netlist ${TOP_MODULE} using CocoAlma"

# Parse
${ALMA_TOP}/parse.py --top-module ${TOP_MODULE} \
--log-yosys \
--synthesis-template ${REPO_TOP}/hw/ip/aes/pre_sca/alma_post_syn/yosys_synth_template.txt \
--netlist ${OUTPUT_DIR}/circuit.v \
--label ${OUTPUT_DIR}/labels.txt \
--json ${OUTPUT_DIR}/circuit.json \
--source ${AES_SBOX_NETLIST_FILE} ${OUTPUT_DIR}/modified_cell_library.v

# Label
sed -i 's/\(data_i\s\[\)\([0-9]\+:0\)\(\]\s=\s\)unimportant/\1\2\3secret \2/g' ${OUTPUT_DIR}/labels.txt
sed -i 's/\(mask_i\s\[\)\([0-9]\+:0\)\(\]\s=\s\)unimportant/\1\2\3secret \2/g' ${OUTPUT_DIR}/labels.txt
sed -i 's/\(prd_i\s\[[0-9]\+:0\]\s=\s\)unimportant/\1static_random/g' ${OUTPUT_DIR}/labels.txt

# Trace
python3 ${ALMA_TOP}/trace.py --testbench ${REPO_TOP}/hw/ip/aes/pre_sca/alma/cpp/verilator_tb_${TESTBENCH}.cpp \
  --netlist ${OUTPUT_DIR}/circuit.v --c-compiler gcc -o ${OUTPUT_DIR}/circuit

# Verify
python3 ${ALMA_TOP}/verify.py --json ${OUTPUT_DIR}/circuit.json \
  --label ${OUTPUT_DIR}/labels.txt \
  --top-module ${TOP_MODULE} \
  --vcd ${OUTPUT_DIR}/tmp.vcd \
  --rst-name rst_ni --rst-phase 0 \
  --mode transient \
  --glitch-behavior loose \
  --cycles 6 \
  --probing-model classic \
  --checking-mode per-secret
