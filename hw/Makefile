# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

CUR_DIR := $(shell dirname $(realpath $(lastword $(MAKEFILE_LIST))))
PRJ_DIR := $(realpath ${CUR_DIR}/../)
export PRJ_DIR

REG_OUTPUT_DIR    ?= ${PRJ_DIR}/build/regs-generated
REG_OUTPUT_DV_DIR ?= ${REG_OUTPUT_DIR}/dv
REG_OUTPUT_SW_DIR ?= ${REG_OUTPUT_DIR}/sw

IPS ?= aes           \
       adc_ctrl      \
       alert_handler \
       aon_timer     \
       clkmgr        \
       entropy_src   \
       csrng         \
       edn           \
       flash_ctrl    \
       gpio          \
       hmac          \
       kmac          \
       i2c           \
       keymgr        \
       lc_ctrl       \
       otp_ctrl      \
       pattgen       \
       pinmux        \
       pwm           \
       pwrmgr        \
       rom_ctrl      \
       rstmgr        \
       rv_core_ibex  \
       rv_dm         \
       rv_plic       \
       rv_timer      \
       sensor_ctrl   \
       spi_device    \
       spi_host      \
       sram_ctrl     \
       sysrst_ctrl   \
       trial1        \
       otbn          \
       uart          \
       usbdev        \
       usbuart

TOPS ?= top_earlgrey

# conditional flags
VERBOSE ?= 0
toolflags ?=
ifeq ($(VERBOSE),1)
  toolflags      += -v
endif

dir_hjson = data

hjson_for_ip = ${PRJ_DIR}/hw/ip/$(1)/$(dir_hjson)/$(1).hjson

# IPs that have a directory in hw/ip
local_ips := \
  $(foreach i,$(IPS),$(if $(wildcard $(call hjson_for_ip,$(i))),$(i)))

# Per-IP targets (all phonies)
ips_reg        = $(addsuffix _reg, $(local_ips))
ips_reg_header = $(addsuffix _reg_header, $(local_ips))
ips_reg_rust   = $(addsuffix _reg_constants, $(local_ips))

# Per-top targets (all phonies)
tops_gen = $(addsuffix _gen,$(TOPS))
tops_reg = $(addsuffix _reg,$(TOPS))

.PHONY: $(ips_reg) $(ips_reg_header) $(ips_reg_rust) $(tops_gen) $(tops_reg)

all: $(ips_reg) $(tops_gen) $(tops_reg) banner

banner:
	@echo "############################################"
	@echo "Note: Regs for DV & SW are now generated at:"
	@echo "${REG_OUTPUT_DIR}"
	@echo "############################################"

regs: $(ips_reg) $(tops_reg) banner

pre_reg:
	mkdir -p ${REG_OUTPUT_DIR}
	mkdir -p ${REG_OUTPUT_DV_DIR}
	mkdir -p ${REG_OUTPUT_SW_DIR}
	if ! [ -z "$(TOCK_ROOT)" ]; then \
		mkdir -p ${TOCK_ROOT}/chips/lowrisc/src/reg_constants; \
	fi

blk-gen-script = $(PRJ_DIR)/hw/ip/$*/util/$*_gen.py
blk-hjson      = $(PRJ_DIR)/hw/ip/$*/$(dir_hjson)/$*.hjson

# If the ip has a local generation script, run it first. This will
# require all blocks to use a consistent naming. This should be hooked
# into ipgen (see #5636) for completeness.
$(ips_reg): %_reg: pre_reg otp-mmap lc-state-enc
	$(if $(wildcard $(blk-gen-script)),$(blk-gen-script))
	${PRJ_DIR}/util/regtool.py ${toolflags} -r $(blk-hjson)
	${PRJ_DIR}/util/regtool.py -s -t ${REG_OUTPUT_DV_DIR} $(blk-hjson)

otp-mmap:
	cd ${PRJ_DIR} && ./util/design/gen-otp-mmap.py

lc-state-enc:
	cd ${PRJ_DIR} && ./util/design/gen-lc-state-enc.py

regs-header: $(ips_reg_header) banner

$(ips_reg_header): %_reg_header: pre_reg
	${PRJ_DIR}/util/regtool.py -D -o ${REG_OUTPUT_SW_DIR}/$*_reg_headers.h $(blk-hjson)

regs-rust: $(ips_reg_rust) banner

$(ips_reg_rust): %_reg_constants: pre_reg
	${PRJ_DIR}/util/regtool.py -R -o ${REG_OUTPUT_SW_DIR}/$@.rs $(blk-hjson); \
	if ! [ -z "$(TOCK_ROOT)" ]; then \
	  cp ${REG_OUTPUT_SW_DIR}/$@.rs ${TOCK_ROOT}/chips/lowrisc/src/reg_constants; \
	fi

clean-regs-header:
	rm -r -f ${REG_OUTPUT_SW_DIR}

top: $(tops_gen) $(tops_reg)
$(tops_gen):
	$(eval $@_TOP := $(strip $(foreach top,$(TOPS),$(findstring $(top),$@))))
	${PRJ_DIR}/util/topgen.py -t ${PRJ_DIR}/hw/$($@_TOP)/data/$($@_TOP).hjson \
		-o ${PRJ_DIR}/hw/$($@_TOP)/ ${toolflags}

$(tops_reg): pre_reg
	$(eval $@_TOP := $(strip $(foreach top,$(TOPS),$(findstring $(top),$@))))
	mkdir -p ${REG_OUTPUT_DV_DIR}/$($@_TOP)
	${PRJ_DIR}/util/topgen.py -t ${PRJ_DIR}/hw/$($@_TOP)/data/$($@_TOP).hjson \
		-r -o ${REG_OUTPUT_DV_DIR}/$($@_TOP) ${toolflags}


.PHONY: all banner otp-mmap lc-state-enc
