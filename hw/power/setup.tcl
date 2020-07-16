# Google Confidential

# Technology setup script for TSMC40ULPEF WLM-based synthesis flow
# See also https://docs.google.com/document/d/1I9R066xZKUuqZxcXhFYtmZW2EC8MBUrTYFDsNT6cNIE
# for more info on the Earlgrey chip specifications.

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
    "io_gppr_cen40fl_t25_mv11_mv33_fs33_svt_dr_${PADS_CORNER}.db" ]

# this appends all ram macros currently wrapped in the prim library
source ${CONFIG_PATH}/ram-macros-setup.tcl

set_app_var link_library ${target_library}

set LOAD_LIB "${STD_CELL_VARIANT}_${STDCELL_CORNER}"
