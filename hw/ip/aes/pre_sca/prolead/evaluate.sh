#!/bin/bash
# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

# Script for evaluating e.g. the masking implementation in combination with the PRNG inside the AES
# cipher core using PROLEAD.

set -e

# Argument parsing
if [[ "$#" -gt 0 ]]; then
  TOP_MODULE=$1
else
  TOP_MODULE=aes_cipher_core
fi
if [[ "$#" -gt 1 ]]; then
  NETLIST_DIR=$2
else
  NETLIST_DIR="${REPO_TOP}/hw/ip/aes/pre_syn/syn_out/latest/generated"
fi

# Create results directory.
OUT_DIR_PREFIX="out/${TOP_MODULE}"
OUT_DIR=$(date +"${OUT_DIR_PREFIX}_%Y_%m_%d_%H_%M_%S")
mkdir -p ${OUT_DIR}
rm -f out/latest
ln -s "${OUT_DIR#out/}" out/latest

# Launch the tool.
PROLEAD -lf library.lib -ln NANG45 \
        -mn ${TOP_MODULE} \
        -df "${NETLIST_DIR}/${TOP_MODULE}_netlist.v" \
        -cf "${TOP_MODULE}_config.set" \
        -rf ${OUT_DIR} \
        2>&1 | tee "${OUT_DIR}/log.txt"
