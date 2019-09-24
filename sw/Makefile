# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

####################################################################################################
## Generate a baremetal application for the microcontroller                                       ##
## Mandatory variables that need to be set over the command line:                                 ##
## SW_DIR:       this is the partial directory path to the SW test being built starting from sw/  ##
##               ex: if running hello_world.c, then SW_DIR=examples/hello_world                   ##
##               At this location, there needs to be a 'srcs.mk' file that contains the list of   ##
##               SW_SRCS to be built for that SW test.                                            ##
## SW_NAME:      This is the name of the SW test begin run. Optional if SW_DIR name (last dir) is ##
##               the same as the SW test name.                                                    ##
## TARGET:       Target for which the sw is cross-compiled - dv|fpga                              ##
##                                                                                                ##
## Optional variables:                                                                            ##
## SW_BUILD_DIR: This is the output location for generating all sources                           ##
## SW_FLAGS      Global args to pass on to the compiler                                           ##
## SW_OPTS       Global args to pass on to the sub-make commands                                  ##
####################################################################################################


# Generate a baremetal application for the microcontroller
SW_ROOT_DIR   := $(shell dirname $(realpath $(lastword $(MAKEFILE_LIST))))
SW_DIR        ?= examples/hello_world

# SW build targets (dv or fpga)
TARGET        ?= fpga

# sources
STANDALONE_SW ?= 0
include ${SW_DIR}/srcs.mk
include exts/common/srcs.mk
include lib/srcs.mk
include util/srcs.mk

# common options and rules
include opts.mk
include rules.mk
