# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
#
# Generate a baremetal application for the microcontroller

DIF_SRCS     = uart.c gpio.c spi_device.c flash_ctrl.c hmac.c usbdev.c rv_timer.c
EXT_SRCS     = usb_controlep.c usb_simpleserial.c irq.c handler.c hw_sha256.c
EXT_ASMS     = irq_vectors.S
GENHDRS     := ${DIF_SRCS:.c=_regs.h}
GENHDR_BASE := ${DIF_SRCS:.c=}
ARCH         = rv32imc
# ARCH = rv32im # to disable compressed instructions

RV_TOOLS    ?= /tools/riscv/bin

INCS        += -I../vendor
CC          := ${RV_TOOLS}/riscv32-unknown-elf-gcc
CFLAGS      ?= -Wall -g -Os -march=$(ARCH) -mabi=ilp32 -static -mcmodel=medany \
               -fvisibility=hidden -nostdlib -nostartfiles $(INCS)


ifeq ($(SIM),1)
  CFLAGS    += -DSIMULATION
endif

AR          := $(subst gcc,ar,$(wordlist 1,1,$(CC)))
ARFLAGS     := rc

REGTOOL      = ../../util/regtool.py

OBJS        := ${DIF_SRCS:.c=.o} ${EXT_SRCS:.c=.o} ${EXT_ASMS:.S=.o}
DEPS         = $(OBJS:%.o=%.d)

OUTFILES     = libot.a

$(OUTFILES): $(OBJS)
	$(AR) $(ARFLAGS) $@ $(OBJS)

all: $(OUTFILES)

define header_gen
    $1.c: $1_regs.h

    $1_regs.h: ../../hw/ip/$1/doc/*.hjson
	if [ -f ../../hw/ip/$1/doc/$1.hjson ]; then \
		$(REGTOOL) -D -o $1_regs.h ../../hw/ip/$1/doc/$1.hjson ; \
	else \
		$(REGTOOL) -D -o $1_regs.h ../../hw/ip/$1/doc/$1_reg.hjson ; \
	fi
endef
$(foreach f,$(GENHDR_BASE),$(eval $(call header_gen,$f)))

-include $(DEPS)

clean:
	$(RM) *.o *.d $(GENHDRS)

distclean: clean
	$(RM) $(OUTFILES)
