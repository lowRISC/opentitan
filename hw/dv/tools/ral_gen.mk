####################################################################################################
## Copyright lowRISC contributors.                                                                ##
## Licensed under the Apache License, Version 2.0, see LICENSE for details.                       ##
## SPDX-License-Identifier: Apache-2.0                                                            ##
####################################################################################################
# tool and options for generating the UVM RAL model
RAL_SPEC      ?= ${DV_DIR}/../data/${DUT_TOP}.hjson
RAL_MODEL_DIR ?= ${BUILD_DIR}/gen_ral_pkg

RAL_PKG_NAME  ?= ${DUT_TOP}
RAL_TOOL      ?= ${MAKE_ROOT}/gen_ral_pkg.py
RAL_TOOL_OPTS += ${RAL_PKG_NAME} ${RAL_SPEC} -o ${RAL_MODEL_DIR}
