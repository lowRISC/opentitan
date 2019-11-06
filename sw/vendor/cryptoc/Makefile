# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
#
# Generate a baremetal application for the microcontroller

LIB_NAME     = cryptoc
DIF_SRCS     = sha256.c
ARCH         = rv32imc
# ARCH = rv32im # to disable compressed instructions

RV_TOOLS    ?= /tools/riscv/bin/

CC          ?= ${RV_TOOLS}/riscv32-unknown-elf-gcc
CFLAGS      ?= -Wall -g -Os -march=$(ARCH) -mabi=ilp32 -static -mcmodel=medany \
	       -fvisibility=hidden -nostdlib -nostartfiles

ifeq ($(SIM),1)
  CFLAGS    += -DSIMULATION
endif

AR          := $(subst gcc,ar,$(wordlist 1,1,$(CC)))
ARFLAGS     ?= -cvr

OBJS        := ${DIF_SRCS:.c=.o}
DEPS         = $(OBJS:%.o=%.d)

OUTFILES     = lib$(LIB_NAME).a

$(OUTFILES): $(OBJS)
	     $(AR) $(ARFLAGS) $@ $(OBJS)

all: $(OUTFILES)

%.o: %.c
	$(CC) $(CFLAGS) -MMD -c $(INCS) -o $@ $<

-include $(DEPS)

clean:
	$(RM) *.o *.d $(OUTFILES)
