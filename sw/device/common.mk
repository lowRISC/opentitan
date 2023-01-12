# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

COMMON_DIR := $(shell dirname $(realpath $(lastword $(MAKEFILE_LIST))))


common_dir = $(COMMON_DIR)/lib/

lib_dirs = . sw/device/lib/base/ sw/device/lib/arch/ sw/device/lib/runtime/ \
           sw/device/lib/crt/ sw/device/lib/ sw/device/headers/ \
           sw/device/silicon_creator/ sw/device/silicon_creator/lib/base \
           sw/device/silicon_creator/lib/drivers sw/device/silicon_creator/lib \
           sw/device/silicon_creator/rom

COMMON_SRC = $(foreach d, $(lib_dirs), -I$(common_dir)$d)

COMMON_SRCS = $(wildcard $(COMMON_SRC)/*.c)

ROOT = /scratch/mciani/he-soc/hardware/working_dir/opentitan/
INCS=$(foreach d, $(lib_dirs), -I$(ROOT)$d)

# ARCH = rv32im # to disable compressed instructions
ARCH ?= rv32imc

ifdef PROGRAM
PROGRAM_C := $(PROGRAM).c
endif

SRCS = $(COMMON_SRCS) $(PROGRAM_C) $(EXTRA_SRCS)

C_SRCS = $(filter %.c, $(SRCS))
ASM_SRCS = $(filter %.S, $(SRCS))

CC = riscv32-unknown-elf-gcc

OBJCOPY ?= $(subst gcc,objcopy,$(wordlist 1,1,$(CC)))
OBJDUMP ?= $(subst gcc,objdump,$(wordlist 1,1,$(CC)))

LINKER_SCRIPT ?= $(common_dir)../silicon_creator/rom/rom.ld
CRT ?= $(utils_dir)/rom/rom_start.S

CFLAGS ?= -march=$(ARCH) -mabi=ilp32 -static -mcmodel=medany -Wall -g -Os -fvisibility=hidden -nostdlib -nostartfiles -ffreestanding  $(PROGRAM_FLAGS)

OBJS := ${C_SRCS:.c=.o} ${ASM_SRCS:.S=.o} ${CRT:.S=.o}
DEPS = $(OBJS:%.o=%.d)

ifdef PROGRAM
OUTFILES := $(PROGRAM).elf $(PROGRAM).vmem $(PROGRAM).bin $(PROGRAM).dis
else
OUTFILES := $(OBJS)
endif

all: $(OUTFILES)

$(PROGRAM).elf: $(OBJS) $(LINKER_SCRIPT)
	$(CC)  $(CFLAGS) -T $(LINKER_SCRIPT) $(OBJS) -o $@ $(LIBS)

%.dis: %.elf
	$(OBJDUMP) -fhSD $^ > $@

# Note: this target requires the srecord package to be installed.
# XXX: This could be replaced by objcopy once
# https://sourceware.org/bugzilla/show_bug.cgi?id=19921
# is widely available.
%.vmem: %.bin
	srec_cat $^ -binary -offset 0x0000 -byte-swap 4 -o $@ -vmem

%.bin: %.elf
	$(OBJCOPY) -O binary $^ $@

%.o: %.c
	$(CC) $(CFLAGS) -MMD -c $(INCS) -o $@ $<

%.o: %.S
	$(CC) $(CFLAGS) -MMD -c $(INCS) -o $@ $<

clean:
	$(RM) -f *.d
	$(RM) -f *.o

distclean: clean
	$(RM) -f $(OUTFILES)
