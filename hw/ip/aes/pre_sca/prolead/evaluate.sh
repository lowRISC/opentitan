#!/bin/bash
# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

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
if [[ "$#" -gt 2 ]]; then
  PROLEAD_BIN="$3"
else
  PROLEAD_BIN="${PROLEAD_BIN:-PROLEAD}"
fi

# Create results directory.
OUT_DIR_PREFIX="out/${TOP_MODULE}"
OUT_DIR=$(date +"${OUT_DIR_PREFIX}_%Y_%m_%d_%H_%M_%S")
mkdir -p ${OUT_DIR}
rm -f out/latest
ln -s "${OUT_DIR#out/}" out/latest

NETLIST_PATH="${NETLIST_FILE:-${NETLIST_DIR}/${TOP_MODULE}_netlist.v}"
LIBRARY_PATH="${LIBRARY_FILE:-library.lib}"
CONFIG_PATH="${CONFIG_FILE:-${TOP_MODULE}_config.set}"

# Launch the tool.
"$PROLEAD_BIN" -lf "$LIBRARY_PATH" -ln NANG45 \
        -mn ${TOP_MODULE} \
        -df "$NETLIST_PATH" \
        -cf "$CONFIG_PATH" \
        -rf ${OUT_DIR} \
        2>&1 | tee "${OUT_DIR}/log.txt"

EXIT_CODE=${PIPESTATUS[0]}

if [ $EXIT_CODE -ne 0 ]; then
    echo "Error: PROLEAD failed with exit code $EXIT_CODE"
    exit $EXIT_CODE
fi

if [[ -n "${MAX_LEAKAGE_THRESHOLD}" ]]; then
    echo "---------------------------------------------------"
    echo "Verifying leakage against threshold: ${MAX_LEAKAGE_THRESHOLD}"

    if ! awk -F'|' -v threshold="${MAX_LEAKAGE_THRESHOLD}" '
        /OKAY/ || /LEAKAGE/ {
            gsub(/ /, "", $(NF-2));
            raw_val = $(NF-2);

            if (raw_val !~ /^[-+]?[0-9]*\.?[0-9]+([eE][-+]?[0-9]+)?$/) {
                exit 1;
            }

            if (raw_val + 0.0 > threshold) {
                exit 1;
            }
        }
    ' "${OUT_DIR}/log.txt"; then
        echo "TEST FAILED"
        exit 1
    else
        echo "SUCCESS"
    fi
fi
