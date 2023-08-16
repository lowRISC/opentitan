# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

CUR_DIR := $(shell dirname $(realpath $(lastword $(MAKEFILE_LIST))))
PRJ_DIR := $(realpath ${CUR_DIR}/../)

REG_OUTPUT_DIR    ?= ${PRJ_DIR}/build/regs-generated
REG_OUTPUT_DV_DIR ?= ${REG_OUTPUT_DIR}/dv
REG_OUTPUT_SW_DIR ?= ${REG_OUTPUT_DIR}/sw
REG_OUTPUT_AUTOGEN_DIR ?= ${PRJ_DIR}/build/autogen

IPS ?= aes           \
       adc_ctrl      \
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
       rv_timer      \
       sensor_ctrl   \
       spi_device    \
       spi_host      \
       sram_ctrl     \
       sysrst_ctrl   \
       trial1        \
       otbn          \
       uart          \
       usbdev

TOPS ?= top_earlgrey

USE_BUFFER ?= 0

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
ips_reg_rust   = $(foreach ip,$(local_ips),$(REG_OUTPUT_SW_DIR)/$(ip)_reg_constants.rs)

# Per-top targets (all phonies)
tops_gen = $(addsuffix _gen,$(TOPS))
tops_reg = $(addsuffix _reg,$(TOPS))
tops_rust_gen = $(addsuffix _gen,$(TOPS))

# Targets for installing files into TOCK_ROOT (empty if TOCK_ROOT is not defined)
ifneq ($(TOCK_ROOT),)
tock_rust_destdir    := $(TOCK_ROOT)/chips/lowrisc/src/reg_constants
ips_reg_rust_install := $(addprefix $(tock_rust_destdir)/,$(notdir $(ips_reg_rust)))

$(tock_rust_destdir):
	mkdir -p $@
endif

.PHONY: $(ips_reg) $(ips_reg_header) $(ips_reg_rust) $(tops_gen) $(tops_reg)

all: $(ips_reg) $(tops_gen) $(tops_reg)

regs: $(ips_reg) $(tops_reg)

$(REG_OUTPUT_DV_DIR) $(REG_OUTPUT_SW_DIR): %:
	mkdir -p $@

blk-gen-script = $(PRJ_DIR)/hw/ip/$*/util/$*_gen.py
blk-hjson      = $(PRJ_DIR)/hw/ip/$*/$(dir_hjson)/$*.hjson

# If the ip has a local generation script, run it first. This will
# require all blocks to use a consistent naming. This should be hooked
# into ipgen (see #5636) for completeness.
$(ips_reg): %_reg: | $(REG_OUTPUT_DV_DIR)
	$(if $(wildcard $(blk-gen-script)),$(blk-gen-script))
	${PRJ_DIR}/util/regtool.py ${toolflags} -r $(blk-hjson)
	${PRJ_DIR}/util/regtool.py --sec-cm-testplan $(blk-hjson)
	${PRJ_DIR}/util/regtool.py -s -t $(REG_OUTPUT_DV_DIR) $(blk-hjson)

# Register generation for otp_ctrl also depends on running gen-otp-mmap.py
.PHONY: otp-mmap
$(filter otp_ctrl_reg,$(ips_reg)): otp-mmap
otp-mmap:
	cd ${PRJ_DIR} && ./util/design/gen-otp-mmap.py ${OTP_MMAP_BUFER}

# Register generation for lc_ctrl also depends on running gen-lc-state-enc.py
.PHONY: lc-state-enc
$(filter lc_ctrl_reg,$(ips_reg)): lc-state-enc
lc-state-enc:
	cd ${PRJ_DIR} && ./util/design/gen-lc-state-enc.py ${LC_BUFFER}

regs-header: $(ips_reg_header)

$(ips_reg_header): %_reg_header: | $(REG_OUTPUT_SW_DIR)
	${PRJ_DIR}/util/regtool.py -D -o $(REG_OUTPUT_SW_DIR)/$*_reg_headers.h $(blk-hjson)

regs-rust: $(ips_reg_rust_install) $(ips_reg_rust)

$(ips_reg_rust): $(REG_OUTPUT_SW_DIR)/%_reg_constants.rs: | $(REG_OUTPUT_SW_DIR)
	${PRJ_DIR}/util/regtool.py -R -o $@ $(blk-hjson)

$(ips_reg_rust_install): $(tock_rust_destdir)/%: $(REG_OUTPUT_SW_DIR)/% | $(tock_rust_destdir)
	cp $< $@

clean-regs-header:
	rm -r -f ${REG_OUTPUT_SW_DIR}

top-hjson = $(PRJ_DIR)/hw/$*/data/$*.hjson
version_out_dir = $(PRJ_DIR)/build
version_path = $(version_out_dir)/workspace_status.txt
top_chip_hjson = $(PRJ_DIR)/hw/$(TOPS)/data/$(TOPS).hjson

$(version_out_dir):
	mkdir -p $@

workspace_status: $(version_out_dir)
	${PRJ_DIR}/util/get_workspace_status.sh > ${version_path}

topgen_rust: workspace_status
	mkdir -p ${REG_OUTPUT_AUTOGEN_DIR}
	${PRJ_DIR}/util/topgen.py -t $(top_chip_hjson) --rust-only -o ${REG_OUTPUT_AUTOGEN_DIR}/ --version-stamp ${version_path} ${toolflags}

topgen_rust_pkg: topgen_rust
	tar -C ${REG_OUTPUT_AUTOGEN_DIR}/sw/autogen/ -cvf ${REG_OUTPUT_AUTOGEN_DIR}/chip_${TOPS}.tar chip

top: $(tops_gen) $(tops_reg)
$(tops_gen): %_gen:
	${PRJ_DIR}/util/topgen.py -t $(top-hjson) -o ${PRJ_DIR}/hw/$*/ ${toolflags}

$(tops_reg): %_reg:
	mkdir -p ${REG_OUTPUT_DV_DIR}/$*
	${PRJ_DIR}/util/topgen.py -t $(top-hjson) -r -o ${REG_OUTPUT_DV_DIR}/$* ${toolflags}


.PHONY: all
