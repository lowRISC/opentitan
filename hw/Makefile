CUR_DIR := $(shell dirname $(realpath $(lastword $(MAKEFILE_LIST))))
PRJ_DIR := $(realpath ${CUR_DIR}/../)
export PRJ_DIR

REG_OUTPUT_DIR    ?= ${PRJ_DIR}/build/regs-generated
REG_OUTPUT_DV_DIR ?= ${REG_OUTPUT_DIR}/dv
REG_OUTPUT_SW_DIR ?= ${REG_OUTPUT_DIR}/sw
REG_OUTPUT_FPV_CSR_DIR ?= ${REG_OUTPUT_DIR}/fpv/vip

IPS ?= uart          \
       gpio          \
       rv_plic       \
       flash_ctrl    \
       spi_device    \
       rv_timer      \
       hmac          \
       usbuart       \
       alert_handler \
       pinmux        \
       padctrl       \
       nmi_gen

TOPS ?= top_earlgrey

# conditional flags
VERBOSE ?= 0
toolflags ?=
ifeq ($(VERBOSE),1)
  toolflags      += -v
endif

dir_hjson = data

dynips_reg = $(addsuffix _reg, $(IPS))

ips_reg = $(addsuffix _reg, $(IPS))

ips_reg_header = $(addsuffix _reg_header, $(IPS))

tops_gen = $(addsuffix _gen,$(TOPS))

tops_reg = $(addsuffix _reg,$(TOPS))

tops_svd = $(addsuffix _svd,$(TOPS))

all: $(dynips_reg) $(tops_gen) $(tops_reg) banner

banner:
	@echo "############################################"
	@echo "Note: Regs for DV & SW are now generated at:"
	@echo "${REG_OUTPUT_DIR}"
	@echo "############################################"

regs: $(dynips_reg) $(tops_reg) banner

pre_reg:
	mkdir -p ${REG_OUTPUT_DIR}
	mkdir -p ${REG_OUTPUT_DV_DIR}
	mkdir -p ${REG_OUTPUT_SW_DIR}

$(ips_reg): pre_reg
	if [ -f ${PRJ_DIR}/hw/ip/$(subst _reg,,$@)/$(dir_hjson)/$(subst _reg,,$@).hjson ]; then \
		${PRJ_DIR}/util/regtool.py -r ${PRJ_DIR}/hw/ip/$(subst _reg,,$@)/$(dir_hjson)/$(subst _reg,,$@).hjson; \
		${PRJ_DIR}/util/regtool.py -s -t ${REG_OUTPUT_DV_DIR} \
		  ${PRJ_DIR}/hw/ip/$(subst _reg,,$@)/$(dir_hjson)/$(subst _reg,,$@).hjson; \
		mkdir -p ${PRJ_DIR}/hw/ip/$(subst _reg,,$@)/fpv/vip; \
		${PRJ_DIR}/util/regtool.py -f -t ${PRJ_DIR}/hw/ip/$(subst _reg,,$@)/fpv/vip/ \
		  ${PRJ_DIR}/hw/ip/$(subst _reg,,$@)/$(dir_hjson)/$(subst _reg,,$@).hjson; \
	fi

regs-header: $(ips_reg_header) banner

$(ips_reg_header): pre_reg
	if [ -f ${PRJ_DIR}/hw/ip/$(subst _reg_header,,$@)/$(dir_hjson)/$(subst _reg_header,,$@).hjson ]; then \
		${PRJ_DIR}/util/regtool.py -D -o ${REG_OUTPUT_SW_DIR}/$(subst _reg_header,_reg_headers,$@).h\
		${PRJ_DIR}/hw/ip/$(subst _reg_header,,$@)/$(dir_hjson)/$(subst _reg_header,,$@).hjson; \
	fi

clean-regs-header:
	rm -r -f ${REG_OUTPUT_SW_DIR}

top: $(tops_gen) $(tops_reg)
$(tops_gen):
	$(eval $@_TOP := $(strip $(foreach top,$(TOPS),$(findstring $(top),$@))))
	${PRJ_DIR}/util/topgen.py -t ${PRJ_DIR}/hw/$($@_TOP)/data/$($@_TOP).hjson \
		--tpl ${PRJ_DIR}/hw/$($@_TOP)/data/ \
		-o ${PRJ_DIR}/hw/$($@_TOP)/ ${toolflags}

$(tops_reg): pre_reg
	$(eval $@_TOP := $(strip $(foreach top,$(TOPS),$(findstring $(top),$@))))
	mkdir -p ${REG_OUTPUT_DV_DIR}/$($@_TOP)
	${PRJ_DIR}/util/topgen.py -t ${PRJ_DIR}/hw/$($@_TOP)/data/$($@_TOP).hjson \
		-r -o ${REG_OUTPUT_DV_DIR}/$($@_TOP) ${toolflags}

$(tops_svd): $(foreach TOP,$(TOPS),${PRJ_DIR}/hw/$(TOP)/data/$(TOP).svd)
%.svd: %.hjson $(foreach IP,$(IPS),${PRJ_DIR}/hw/ip/$(IP)/data/$(IP).hjson)
	${PRJ_DIR}/util/topgen.py --svd-only $@ --topcfg $< \
		--no-top --no-xbar --no-plic --no-gen-hjson

.SECONDARY: ${PRJ_DIR}/hw/top_earlgrey/data/top_earlgrey.svd
cargo: ${PRJ_DIR}/hw/top_earlgrey/data/src/lib.rs
	(cd ${PRJ_DIR}/hw/top_earlgrey/data/ && cargo build)
.PHONY: cargo

# Example rule to generate `top_earlgrey.rs` from `top_earlgrey.svd`.
# There's no way to specify the output path, so `cd` there first. Not
# included in default build.
${PRJ_DIR}/hw/top_earlgrey/data/src/lib.rs: ${PRJ_DIR}/hw/top_earlgrey/data/top_earlgrey.svd
	(cd $(@D) && svd2rust --target=riscv -i ../$(<F))

.PHONY: all banner $(ips_reg) $(tops_gen) $(tops_svd) $(ips_reg_header)
