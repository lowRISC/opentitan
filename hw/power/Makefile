# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
.DEFAULT_GOAL := all

CORE_ROOT ?= ../..
CUR_DIR ?= $(CORE_ROOT)/hw/power
OUT_DIR ?= $(CUR_DIR)/build/lowrisc_systems_top_earlgrey*

all: lint

gen_sv_flist:
	rm -rf $(CUR_DIR)/build/
	fusesoc --cores-root $(CORE_ROOT) run --target=syn --tool=icarus --setup lowrisc:systems:top_earlgrey
	cp $(CORE_ROOT)/hw/foundry/syn/dc/lib-setup.tcl $(OUT_DIR)/syn-icarus
	cp $(CORE_ROOT)/hw/foundry/syn/dc/ram-macros-setup.tcl $(OUT_DIR)/syn-icarus
	cp $(CUR_DIR)/setup.tcl $(OUT_DIR)/syn-icarus
	cp $(CUR_DIR)/top_earlgrey.upf $(OUT_DIR)/syn-icarus
	cp $(CUR_DIR)/run-vclp.tcl $(OUT_DIR)/syn-icarus


lint: gen_sv_flist
	cd $(OUT_DIR)/syn-icarus && \
	vc_static_shell -batch -no_ui -f run-vclp.tcl -output_log_file vclp.log
