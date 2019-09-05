CUR_DIR := $(shell dirname $(realpath $(lastword $(MAKEFILE_LIST))))
PRJ_DIR := $(realpath ${CUR_DIR}/../)
export PRJ_DIR

IPS ?= uart       \
       gpio       \
       rv_plic    \
       flash_ctrl \
       spi_device \
       rv_timer   \
       hmac       \
       usbuart

TOPS ?= top_earlgrey

ips_reg = $(addsuffix _reg, $(IPS))

tops_gen = $(addsuffix _gen,$(TOPS))

all: $(ips_reg)

regs: $(ips_reg)

$(ips_reg):
	if [ -f ${PRJ_DIR}/hw/ip/$(subst _reg,,$@)/doc/$(subst _reg,,$@).hjson ]; then \
		${PRJ_DIR}/util/regtool.py -r ${PRJ_DIR}/hw/ip/$(subst _reg,,$@)/doc/$(subst _reg,,$@).hjson; \
		${PRJ_DIR}/util/regtool.py -D -o ${PRJ_DIR}/hw/ip/$(subst _reg,,$@)/sw/$(subst _reg,_regs,$@).h\
		  ${PRJ_DIR}/hw/ip/$(subst _reg,,$@)/doc/$(subst _reg,,$@).hjson; \
		${PRJ_DIR}/util/regtool.py -s -t ${PRJ_DIR}/hw/ip/$(subst _reg,,$@)/dv/env \
		  ${PRJ_DIR}/hw/ip/$(subst _reg,,$@)//doc/$(subst _reg,,$@).hjson; \
	else if [ -f ${PRJ_DIR}/hw/ip/$(subst _reg,,$@)/doc/$@.hjson ]; then \
		${PRJ_DIR}/util/regtool.py -r ${PRJ_DIR}/hw/ip/$(subst _reg,,$@)/doc/$@.hjson; \
		${PRJ_DIR}/util/regtool.py -D -o ${PRJ_DIR}/hw/ip/$(subst _reg,,$@)/sw/$(subst _reg,_regs,$@).h \
		${PRJ_DIR}/hw/ip/$(subst _reg,,$@)/doc/$@.hjson; \
		${PRJ_DIR}/util/regtool.py -s -t ${PRJ_DIR}/hw/ip/$(subst _reg,,$@)/dv/env \
		  ${PRJ_DIR}/hw/ip/$(subst _reg,,$@)//doc/$@.hjson; \
	fi \
	fi

$(tops_gen):
	$(eval $@_TOP := $(strip $(foreach top,$(TOPS),$(findstring $(top),$@))))
	${PRJ_DIR}/util/topgen.py -t ${PRJ_DIR}/hw/$($@_TOP)/doc/$($@_TOP).hjson \
		--tpl ${PRJ_DIR}/hw/$($@_TOP)/doc/$($@_TOP).tpl.sv \
		-o ${PRJ_DIR}/hw/$($@_TOP)/ -v
	${PRJ_DIR}/util/topgen.py -t ${PRJ_DIR}/hw/$($@_TOP)/doc/$($@_TOP).hjson \
		-r -o ${PRJ_DIR}/hw/$($@_TOP)/dv/env/ -v

.PHONY: all $(ips_reg) $(tops_gen)
