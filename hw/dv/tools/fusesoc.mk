####################################################################################################
## Copyright lowRISC contributors.                                                                ##
## Licensed under the Apache License, Version 2.0, see LICENSE for details.                       ##
## SPDX-License-Identifier: Apache-2.0                                                            ##
####################################################################################################
## Make variables specific to FUSESOC tool used for generating the filelist                       ##
## The following Make variables are to be set in the Test Makefile                                ##
## FUSESOC_CORE: the top level fusesoc core file developed for the ip/top level testbench         ##
##               see hw/ip/uart/dv/uart_sim.core as an example                                    ##
## Rest of the Make variables added here are intermeditiate ones used in the flow                 ##
####################################################################################################
# fusesoc tool and options
SV_FLIST_GEN_TOOL  ?= fusesoc
SV_FLIST_GEN_OPTS  += --cores-root ${PROJ_ROOT} --cores-root ${RAL_MODEL_DIR} \
                      run --target=sim --setup ${FUSESOC_CORE}
FUSESOC_CORE_       = $(shell echo "${FUSESOC_CORE}" | tr ':' '_')
SV_FLIST_GEN_DIR    = ${BUILD_DIR}/build/${FUSESOC_CORE_}/sim-vcs
SV_FLIST           := ${SV_FLIST_GEN_DIR}/${FUSESOC_CORE_}.scr
