CUR_DIR := $(shell dirname $(realpath $(lastword $(MAKEFILE_LIST))))
PRJ_DIR := $(realpath ${CUR_DIR}/../)
export PRJ_DIR

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
       padctrl

TOPS ?= top_earlgrey

# conditional flags
VERBOSE ?= 0
toolflags ?=
ifeq ($(VERBOSE),1)
  toolflags      += -v
endif

dir_hjson = data

ips_reg = $(addsuffix _reg, $(IPS))

ips_reg_header = $(addsuffix _reg_header, $(IPS))

tops_gen = $(addsuffix _gen,$(TOPS))

all: $(ips_reg) $(tops_gen)

regs: $(ips_reg)

$(ips_reg):
	if [ -f ${PRJ_DIR}/hw/ip/$(subst _reg,,$@)/$(dir_hjson)/$(subst _reg,,$@).hjson ]; then \
		${PRJ_DIR}/util/regtool.py -r ${PRJ_DIR}/hw/ip/$(subst _reg,,$@)/$(dir_hjson)/$(subst _reg,,$@).hjson; \
		${PRJ_DIR}/util/regtool.py -s -t ${PRJ_DIR}/hw/ip/$(subst _reg,,$@)/dv/env \
		  ${PRJ_DIR}/hw/ip/$(subst _reg,,$@)/$(dir_hjson)/$(subst _reg,,$@).hjson; \
	else if [ -f ${PRJ_DIR}/hw/ip/$(subst _reg,,$@)/$(dir_hjson)/$@.hjson ]; then \
		${PRJ_DIR}/util/regtool.py -r ${PRJ_DIR}/hw/ip/$(subst _reg,,$@)/$(dir_hjson)/$@.hjson; \
		${PRJ_DIR}/util/regtool.py -s -t ${PRJ_DIR}/hw/ip/$(subst _reg,,$@)/dv/env \
		  ${PRJ_DIR}/hw/ip/$(subst _reg,,$@)/$(dir_hjson)/$@.hjson; \
	fi \
	fi

regs-header: $(ips_reg_header)
$(ips_reg_header):
	if [ -f ${PRJ_DIR}/hw/ip/$(subst _reg_header,,$@)/$(dir_hjson)/$(subst _reg_header,,$@).hjson ]; then \
		[[ -d ${PRJ_DIR}/hw/ip/$(subst _reg_header,,$@)/sw ]] || mkdir ${PRJ_DIR}/hw/ip/$(subst _reg_header,,$@)/sw; \
		${PRJ_DIR}/util/regtool.py -D -o ${PRJ_DIR}/hw/ip/$(subst _reg_header,,$@)/sw/$(subst _reg_header,_reg_headers,$@).h\
		${PRJ_DIR}/hw/ip/$(subst _reg_header,,$@)/$(dir_hjson)/$(subst _reg_header,,$@).hjson; \
	else if [ -f ${PRJ_DIR}/hw/ip/$(subst _reg_header,,$@)/$(dir_hjson)/$@.hjson ]; then \
		[[ -d ${PRJ_DIR}/hw/ip/$(subst _reg_header,,$@)/sw ]] || mkdir ${PRJ_DIR}/hw/ip/$(subst _reg_header,,$@)/sw; \
		${PRJ_DIR}/util/regtool.py -D -o ${PRJ_DIR}/hw/ip/$(subst _reg_header,,$@)/sw/$(subst _reg_header,_reg_headers,$@).h \
		${PRJ_DIR}/hw/ip/$(subst _reg_header,,$@)/$(dir_hjson)/$@.hjson; \
	fi \
	fi

clean-regs-header:
	rm -r -f ip/*/sw

$(tops_gen):
	$(eval $@_TOP := $(strip $(foreach top,$(TOPS),$(findstring $(top),$@))))
	${PRJ_DIR}/util/topgen.py -t ${PRJ_DIR}/hw/$($@_TOP)/doc/$($@_TOP).hjson \
		--tpl ${PRJ_DIR}/hw/$($@_TOP)/doc/ \
		-o ${PRJ_DIR}/hw/$($@_TOP)/ ${toolflags}
	${PRJ_DIR}/util/topgen.py -t ${PRJ_DIR}/hw/$($@_TOP)/doc/$($@_TOP).hjson \
		-r -o ${PRJ_DIR}/hw/$($@_TOP)/dv/env/ ${toolflags}

.PHONY: all $(ips_reg) $(tops_gen) $(ips_reg_header)
