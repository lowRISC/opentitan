# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
#
# Simple tcl script to setup power lint flow

########################
##   LIBRARY PATHS    ##
########################

source lib-setup.tcl

########################
##   Assign Config    ##
########################

# this could eventually be moved into .synopsys_dc.setup
set_app_var search_path [list .      \
    ${STDCELL_DB_PATH}               \
    ${SRAM_DB_PATH}                  \
    ${PADS_DB_PATH}                  ]

set_app_var target_library [list                                  \
    "${STD_CELL_VARIANT}_${STDCELL_CORNER}.db"                    \
    "${PAD_LIB_VARIANT}_${PADS_CORNER}.db" ]

# this appends all ram macros currently wrapped in the prim library
source ${CONFIG_PATH}/ram-macros-setup.tcl

set_app_var link_library ${target_library}

set LOAD_LIB "${STD_CELL_VARIANT}_${STDCELL_CORNER}"
