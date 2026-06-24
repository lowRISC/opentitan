#!/usr/bin/env bash
# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

# Script for evaluating secure gadget implementations in OTBN using PROLEAD.

set -e

CONFIG_SUFFIX=""
# NETLIST_MODULE: the synthesized top module name (determines netlist filename).
# CONFIG_MODULE: the module name embedded in the ProLEAD config filename.
# For most targets these are the same; for mask_acc_* the DUT is synthesized
# directly (no SCA wrapper) so the netlist module differs from the config name.
case "$1" in
  hpc2)
    NETLIST_MODULE=prim_hpc2_sca_wrapper
    ;;
  hpc2o)
    NETLIST_MODULE=prim_hpc2o_sca_wrapper
    ;;
  hpc3)
    NETLIST_MODULE=prim_hpc3_sca_wrapper
    ;;
  hpc3o)
    NETLIST_MODULE=prim_hpc3o_sca_wrapper
    ;;
  sec_add)
    NETLIST_MODULE=otbn_sec_add_sca_wrapper
    ;;
  mask_acc_sec_add)
    NETLIST_MODULE=otbn_mask_accelerator
    CONFIG_MODULE=otbn_mask_accelerator_sca_wrapper
    CONFIG_SUFFIX=_sec_add
    ;;
  mask_acc_sec_add_mod)
    NETLIST_MODULE=otbn_mask_accelerator
    CONFIG_MODULE=otbn_mask_accelerator_sca_wrapper
    CONFIG_SUFFIX=_sec_add_mod
    ;;
  mask_acc_a2b)
    NETLIST_MODULE=otbn_mask_accelerator
    CONFIG_MODULE=otbn_mask_accelerator_sca_wrapper
    CONFIG_SUFFIX=_a2b
    ;;
  *)
    NETLIST_MODULE=otbn_mask_accelerator
    CONFIG_MODULE=otbn_mask_accelerator_sca_wrapper
    CONFIG_SUFFIX=_b2a
    ;;
esac
# Default: config file is named after the netlist module.
CONFIG_MODULE="${CONFIG_MODULE:-${NETLIST_MODULE}}"

if [[ "$#" -gt 1 ]]; then
  NETLIST_DIR=$2
else
  NETLIST_DIR="${REPO_TOP}/hw/ip/otbn/pre_syn/syn_out/latest/generated"
fi

perl -i -pe "s/(\d+)'h0+/ join(', ', ('1\\'b0') x \$1) /ge" ${NETLIST_DIR}/${NETLIST_MODULE}_netlist.v

# Create results directory.
OUT_DIR_PREFIX="out/${NETLIST_MODULE}${CONFIG_SUFFIX}"
OUT_DIR=$(date +"${OUT_DIR_PREFIX}_%Y_%m_%d_%H_%M_%S")
mkdir -p ${OUT_DIR}
rm -f out/latest
ln -s "${OUT_DIR#out/}" out/latest

CONFIG_SRC=${REPO_TOP}/hw/ip/otbn/pre_sca/prolead/server_config_${CONFIG_MODULE}${CONFIG_SUFFIX}.json
echo ${CONFIG_SRC}

# Strip the _comment key (PROLEAD validates all JSON keys strictly).
CONFIG_TMP=$(mktemp --suffix=.json)
grep -v '"_comment"' "${CONFIG_SRC}" > "${CONFIG_TMP}"

# Launch the tool.
PROLEAD -l ${REPO_TOP}/hw/ip/otbn/pre_sca/prolead/nang45.json \
        -n nang45 \
        -d ${NETLIST_DIR}/${NETLIST_MODULE}_netlist.v \
        -m ${NETLIST_MODULE} \
        -rf ${OUT_DIR} \
        -c "${CONFIG_TMP}"
rm -f "${CONFIG_TMP}"
