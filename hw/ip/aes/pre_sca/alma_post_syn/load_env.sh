#!/bin/bash
# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

# This file needs to be sourced into shell as follows:
# `source load_env.sh`

check_dir_exists () {
    if [ ! -d "${1}" ]; then
        echo "${2} needs to be set to the top directory of the ${3}."
    fi
}

check_file_exists () {
    if [ ! -f "${1}" ]; then
        echo "The file pointed by ${2} does not exist."
    fi
}

# `REPO_TOP` should be the top folder for OpenTitan repository and it
# can be sourced from util/build_consts.sh.
check_dir_exists ${REPO_TOP} "REPO_TOP" "OpenTitan repo"

# Set the top folder for foundry repo
export ASIC_TOP="/usr/local/google/home/fatihballi/Documents/asic"
check_dir_exists ${ASIC_TOP} "ASIC_TOP" "foundry repo"

# Set the top folder for CocoAlma
export ALMA_TOP="/usr/local/google/home/fatihballi/Documents/coco-alma"
check_dir_exists ${ALMA_TOP} "ALMA_TOP" "CocoAlma repo"

# The output folder for temporary files created during the flow
export OUTPUT_DIR=/tmp/alma_tmp

# The following paths should not need any modification, however patch and
# netlist files need to be manually placed in the respective folders (since
# they are not part of the public repo).
export SIM_MODEL_FILE=${ASIC_TOP}/vendor/std_cell/verilog/ts40n8ksdst.v
check_file_exists $SIM_MODEL_FILE "SIM_MODEL_FILE"

export AES_SBOX_NETLIST_FILE=${ASIC_TOP}/alma/aes_sbox_SecSBoxImpl4.gv
check_file_exists $AES_SBOX_NETLIST_FILE "AES_SBOX_NETLIST_FILE"

export SIM_PATCH_FILE=${ASIC_TOP}/alma/techlib_patch.v
check_file_exists $SIM_PATCH_FILE "SIM_PATCH_FILE"

# This file will be created during the flow
export MODIFIED_TECHLIB_FILE=${OUTPUT_DIR}/modified_cell_library.v

export TOP_MODULE=aes_sbox_dom
export TESTBENCH=aes_sbox
