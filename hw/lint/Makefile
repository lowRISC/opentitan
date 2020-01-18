# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
#
# Makefile with ascentlint and verilator-lint targets for OpenTitan
#
# TODO: currently we cannot support parallel builds since some fusesoc cores
# define filesets with files outside the current folder (e.g. using relative
# path prefixes such as "../../"). this can cause collisions between parallel
# builds since they are not nicely contained within the same folder. This should
# be solved by reworking the fusesoc core files (especially the top-level one).

CORE_ROOT ?= ../../
REPORT_DIR ?= reports

IPS ?=  ip-aes                 \
        ip-alert_handler       \
        ip-flash_ctrl          \
        ip-gpio                \
        ip-hmac                \
        ip-i2c                 \
        ip-nmi_gen             \
        ip-padctrl             \
        ip-padring             \
        ip-pinmux              \
        ip-rv_core_ibex        \
        ip-rv_dm               \
        ip-rv_plic_example     \
        ip-rv_timer            \
        ip-spi_device          \
        ip-uart                \
        ip-usbdev              \
        ip-usb_fs_nb_pe        \
        ip-usbuart             \
        tlul-socket_1n         \
        tlul-socket_m1         \
        tlul-adapter_reg       \
        tlul-adapter_sram      \
        tlul-sram2tlul         \
        systems-top_earlgrey

ips_lint  = $(addsuffix _lint, $(IPS))
ips_vlint = $(addsuffix _vlint, $(IPS))

######################
# ascentlint targets #
######################

# lint all discovered targets and make a report
all: lint
	$(MAKE) report

lint: clean
	@echo Discovered lint targets:
	@echo -e "\n $(patsubst %,%\\n,$(strip $(ips_lint)))"
	$(MAKE) $(ips_lint)

$(ips_lint):
	rm -rf build
	mkdir -p ${REPORT_DIR}
	-fusesoc --cores-root ${CORE_ROOT} run --target=lint --tool=ascentlint lowrisc:$(subst -,:,$(patsubst %_lint,%,$@))
	cp build/lowrisc_*$(subst -,_,$(patsubst %_lint,%,$@))*/lint-ascentlint/ascentlint.log ${REPORT_DIR}/$(patsubst %_lint,%,$@).log
	cp build/lowrisc_*$(subst -,_,$(patsubst %_lint,%,$@))*/lint-ascentlint/ascentlint.rpt ${REPORT_DIR}/$(patsubst %_lint,%,$@).rpt

# creates a (filtered) summary report from all available ascentlint logs/rpts
# note that lint reports have to be filtered using this script before publishing
# any information from these reports publicly
# note, the filtering script is simplistic ATM and just looks for *.rpt files
# hence we have to temporarily write the output to a file with a different extension
# since otherwise the gen_report script will try to process the summary report as well.
report:
	$(eval TMPFILE=$(shell mktemp))
	rm -f ${REPORT_DIR}/lint_summary.rpt
	./gen_report.sh | tee $(TMPFILE)
	cp $(TMPFILE) ${REPORT_DIR}/lint_summary.rpt
	rm -f $(TMPFILE)

#####################
# verilator targets #
#####################

# lint all discovered targets and make a report
vall: vlint
	$(MAKE) vreport

vlint: clean
	@echo Discovered vlint targets:
	@echo -e "\n $(patsubst %,%\\n,$(strip $(ips_vlint)))"
	$(MAKE) $(ips_vlint)

$(ips_vlint):
	rm -rf build
	mkdir -p ${REPORT_DIR}
	-fusesoc --cores-root ${CORE_ROOT} run --target=lint lowrisc:$(subst -,:,$(patsubst %_vlint,%,$@))
#	cp build/lowrisc_*$(patsubst %_vlint,%,$@)*/vlint-verilator/verilator-lint.rpt ${REPORT_DIR}/$@.rpt

# TODO: add a verilator summary report function
# add a summary report option for verilator
vreport:

##################
# common targets #
##################

clean:
	rm -rf build
	rm -rf ${REPORT_DIR}/*

.PHONY: all lint $(ips_lint) report vall vlint $(ips_vlint) clean
