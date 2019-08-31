# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
#
# Generate a baremetal application for the microcontroller

GENHDRS = uart_regs.h gpio_regs.h spi_device_regs.h flash_ctrl_regs.h

PROGRAM ?= boot_rom
PROGRAM_CFLAGS = -Wall -g -Os
ifeq ($(SIM),1)
  PROGRAM_CFLAGS += -DSIMULATION
endif
ARCH = rv32imc
# ARCH = rv32im # to disable compressed instructions
SRCS = uart.c gpio.c spi_device.c flash_ctrl.c bootstrap.c $(PROGRAM).c
RV_TOOLS ?= /tools/riscv/bin


CC = ${RV_TOOLS}/riscv32-unknown-elf-gcc

OBJCOPY ?= $(subst gcc,objcopy,$(wordlist 1,1,$(CC)))
OBJDUMP ?= $(subst gcc,objdump,$(wordlist 1,1,$(CC)))
REGTOOL = ../../util/regtool.py

LINKER_SCRIPT ?= link.ld
CRT ?= crt0.S
CFLAGS ?= -march=$(ARCH) -mabi=ilp32 -static -mcmodel=medany \
	-fvisibility=hidden -nostdlib -nostartfiles $(PROGRAM_CFLAGS)

OBJS := ${SRCS:.c=.o} ${CRT:.S=.o}
DEPS = $(OBJS:%.o=%.d)

OUTFILES = $(PROGRAM).elf $(PROGRAM).vmem $(PROGRAM).bin $(PROGRAM).dis $(PROGRAM).map

all: $(OUTFILES)

$(PROGRAM).elf: $(OBJS) $(LINKER_SCRIPT)
	$(CC) $(CFLAGS) -T $(LINKER_SCRIPT) $(OBJS) -o $@ $(LIBS) -Xlinker -Map=${PROGRAM}.map

%.dis: %.elf
	$(OBJDUMP) -SD $^ > $@

# Note: this target requires the srecord package to be installed.
# XXX: This could be replaced by objcopy once
# https://sourceware.org/bugzilla/show_bug.cgi?id=19921
# is merged.
# XXX: Currently the start address 0x1000 is hardcoded. It could/should be
# read from the elf file, but is lost in the bin file.
# Switching to objcopy will resolve that as well.
%.vmem: %.bin
	srec_cat $^ -binary -offset 0x0 -byte-swap 4 -o $@ -vmem

%.bin: %.elf
	$(OBJCOPY) -O binary $^ $@

%.o: %.c
	$(CC) $(CFLAGS) -MMD -c $(INCS) -o $@ $<

%.o: %.S
	$(CC) $(CFLAGS) -MMD -c $(INCS) -o $@ $<

# Can't find a way to use % twice in RHS, this based on stackoverflow
GENHDR_BASE = $(subst _regs.h,,$(GENHDRS))
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
	$(RM) -f *.o *.d *.bin *.vmem *.dis *.elf *.map $(GENHDRS)

distclean: clean
	$(RM) -f $(OUTFILES)
