#!/usr/bin/env bash
# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

# Script for evaluating secure gadget implementations in OTBN using PROLEAD.

set -e

case "$1" in
  hpc2)
    TOP_MODULE=prim_hpc2_sca_wrapper
    ;;
  hpc2o)
    TOP_MODULE=prim_hpc2o_sca_wrapper
    ;;
  hpc3)
    TOP_MODULE=prim_hpc3_sca_wrapper
    ;;
  hpc3o)
    TOP_MODULE=prim_hpc3o_sca_wrapper
    ;;
  *)
    # Default case.
    TOP_MODULE=prim_hpc3o_sca_wrapper
    ;;
esac
if [[ "$#" -gt 1 ]]; then
  NETLIST_DIR=$2
else
  NETLIST_DIR="${REPO_TOP}/hw/ip/otbn/pre_syn/syn_out/latest/generated"
fi

perl -i -pe "s/(\d+)'h0+/ join(', ', ('1\\'b0') x \$1) /ge" ${NETLIST_DIR}/${TOP_MODULE}_netlist.v

# Create results directory.
OUT_DIR_PREFIX="out/${TOP_MODULE}"
OUT_DIR=$(date +"${OUT_DIR_PREFIX}_%Y_%m_%d_%H_%M_%S")
mkdir -p ${OUT_DIR}
rm -f out/latest
ln -s "${OUT_DIR#out/}" out/latest

CONFIG_SRC=${REPO_TOP}/hw/ip/otbn/pre_sca/prolead/server_config_${TOP_MODULE}.json
echo ${CONFIG_SRC}

# Strip the _comment key (PROLEAD validates all JSON keys strictly).
CONFIG_TMP=$(mktemp --suffix=.json)
jq 'del(._comment)' "${CONFIG_SRC}" > "${CONFIG_TMP}"

# Launch the tool.
PROLEAD -l ${REPO_TOP}/hw/ip/otbn/pre_sca/prolead/nang45.json \
        -n nang45 \
        -d ${NETLIST_DIR}/${TOP_MODULE}_netlist.v \
        -m ${TOP_MODULE} \
        -rf ${OUT_DIR} \
        -c "${CONFIG_TMP}"
rm -f "${CONFIG_TMP}"
