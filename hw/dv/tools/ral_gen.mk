####################################################################################################
## Copyright lowRISC contributors.                                                                ##
## Licensed under the Apache License, Version 2.0, see LICENSE for details.                       ##
## SPDX-License-Identifier: Apache-2.0                                                            ##
####################################################################################################
# tool and options for generating the UVM RAL model
RAL_TOOL      ?= ${PROJ_ROOT}/util/regtool.py
RAL_MODEL_DIR ?= ${DV_DIR}/env
RAL_TOOL_OPTS += -s -t ${RAL_MODEL_DIR} ${DV_DIR}/../data/${DUT_TOP}.hjson
RAL_MODEL      = ${RAL_MODEL_DIR}/${DUT_TOP}_reg_block.sv
