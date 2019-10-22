#
# Ensure the compiler and necessary executables are on the search PATH
#

#
# Ensure you have set the following Variables
#
#

pipe:= |
empty:=
space:= $(empty) $(empty)

export RISCV_TARGET ?= riscvOVPsim
export RISCV_DEVICE ?= rv32i
export RISCV_PREFIX ?= riscv64-unknown-elf-

RISCV_ISA_ALL = $(shell ls $(ROOTDIR)/riscv-target/$(RISCV_TARGET)/device)
RISCV_ISA_OPT = $(subst $(space),$(pipe),$(RISCV_ISA_ALL))


ifeq ($(RISCV_ISA),)
    RISCV_ISA = rv32i
    DEFAULT_TARGET=all_variant
else
    DEFAULT_TARGET=variant
endif

export ROOTDIR  = $(shell pwd)
export WORK     = $(ROOTDIR)/work
export SUITEDIR = $(ROOTDIR)/riscv-test-suite/$(RISCV_ISA)
export TARGETDIR ?= $(ROOTDIR)/riscv-target

default: $(DEFAULT_TARGET)

variant: simulate verify

all_variant:
	for isa in $(RISCV_ISA_ALL); do \
		echo $$isa; \
		$(MAKE) RISCV_TARGET=$(RISCV_TARGET) RISCV_DEVICE=$$isa RISCV_ISA=$$isa variant; \
                rc=$$?; \
                if [ $$rc -ne 0 ]; then \
			exit $$rc; \
		fi \
	done

simulate:
	make \
		RISCV_TARGET=$(RISCV_TARGET) \
		RISCV_DEVICE=$(RISCV_DEVICE) \
		RISCV_PREFIX=$(RISCV_PREFIX) \
		run -C $(SUITEDIR)

verify:
	riscv-test-env/verify.sh

clean:
	make \
		RISCV_TARGET=$(RISCV_TARGET) \
		RISCV_DEVICE=$(RISCV_DEVICE) \
		RISCV_PREFIX=$(RISCV_PREFIX) \
		clean -C $(SUITEDIR)

help:
	@echo "make"
	@echo "RISCV_TARGET='riscvOVPsim|spike'"
	@echo "RISCV_DEVICE='rv32i|rv32im|...'"
	@echo "RISCV_ISA=$(RISCV_ISA_OPT)"
	@echo "make all_variant // all combinations"

