# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
#
# Generate a baremetal application for the microcontroller

NAME          := coremark
PROGRAM_DIR   := $(shell dirname $(realpath $(lastword $(MAKEFILE_LIST))))
COREMARK_DIR  := $(PROGRAM_DIR)/../../vendor/$(NAME)
COREMARK_PORT := $(PROGRAM_DIR)/top_earlgrey

all:
#	$(MAKE) -C $(LIB_DIR) MAKEFLAGS=$(MAKEFLAGS)
	$(MAKE) -C $(LIB_DIR)
	$(MAKE) -C $(COREMARK_DIR) PORT_DIR=$(COREMARK_PORT)
	$(foreach out, $(OUTFILES), cp $(COREMARK_DIR)/$(out) .;)


distclean:
	$(RM) $(OUTFILES)
	$(MAKE) -C $(LIB_DIR) distclean
	$(MAKE) -C $(COREMARK_DIR) clean PORT_DIR=$(COREMARK_PORT)

include ${PROGRAM_DIR}/../../exts/common/options.mk
