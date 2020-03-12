# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
#
# Makefile with synthesis targets for OpenTitan

CORE_ROOT ?= ../../
REPORT_DIR ?= reports
# this directory contains the library setup file (setup.tcl)
LIB_SETUP_SCRIPT ?= `pwd`/../foundry/syn/dc/setup.tcl
# sources for DC
TOOL_SRCS   = ./tools/dc/start-dc.sh     \
              ./tools/dc/run-syn.tcl     \
              ./tools/dc/constraints.sdc

IPS ?=  ip-aes                 \
        systems-top_earlgrey
#         ip-alert_handler       \
#         ip-flash_ctrl          \
#         ip-gpio                \
#         ip-hmac                \
#         ip-i2c                 \
#         ip-nmi_gen             \
#         ip-padctrl             \
#         ip-padring             \
#         ip-pinmux              \
#         ip-rv_core_ibex        \
#         ip-rv_dm               \
#         ip-rv_plic_example     \
#         ip-rv_timer            \
#         ip-spi_device          \
#         ip-uart                \
#         ip-usbdev              \
#         ip-usb_fs_nb_pe        \
#         ip-usbuart             \
#         tlul-socket_1n         \
#         tlul-socket_m1         \
#         tlul-adapter_reg       \
#         tlul-adapter_sram      \
#         tlul-sram2tlul         \


ips_syn  = $(addsuffix _syn, $(IPS))

######################
# synthesis targets #
######################

all: clean
	@echo Discovered synth targets:
	@echo -e "\n $(patsubst %,%\\n,$(strip $(ips_syn)))"
	$(MAKE) $(ips_lint)

$(ips_syn):
	mkdir -p ${REPORT_DIR}
	fusesoc --cores-root ${CORE_ROOT} run --target=syn --tool=icarus --setup lowrisc:$(subst -,:,$(patsubst %_syn,%,$@))
	cp ${TOOL_SRCS} build/lowrisc_*$(subst -,_,$(patsubst %_syn,%,$@))*/syn-icarus/
	export TOP_ENTITY="$(patsubst ip-%,%,$(patsubst tlul-%,%,$(patsubst systems-%,%,$(patsubst %_syn,%,$@))))" && \
	export LIB_SETUP_SCRIPT=${LIB_SETUP_SCRIPT} && \
	cd build/lowrisc_*$(subst -,_,$(patsubst %_syn,%,$@))*/syn-icarus/ && ./start-dc.sh -f run-syn.tcl
	cp build/lowrisc_*$(subst -,_,$(patsubst %_syn,%,$@))*/syn-icarus/REPORTS/*.rpt ${REPORT_DIR}/

clean:
	rm -rf build
	rm -rf ${REPORT_DIR}/*

.PHONY: all $(ips_syn) clean
