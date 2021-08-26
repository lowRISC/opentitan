# Copyright lowRISC contributors.
# Copyright 2018 Embedded Microprocessor Benchmark Consortium (EEMBC)
# Original Author: Shay Gal-on
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

RV_ISA = rv32im

OUTFILES = $(OPATH)coremark.dis $(OPATH)coremark.map $(OPATH)coremark.vmem

NAME                 = coremark
PORT_CLEAN          := $(OUTFILES)
SIMPLE_SYSTEM_COMMON = ../../examples/sw/simple_system/common
EXT_SRCS             = $(wildcard $(SIMPLE_SYSTEM_COMMON)/*.c)
CRT0				         = $(SIMPLE_SYSTEM_COMMON)/crt0.S
LINKER_SCRIPT        = $(SIMPLE_SYSTEM_COMMON)/link.ld

# Flag : OUTFLAG
#	Use this flag to define how to to get an executable (e.g -o)
OUTFLAG = -o
# Flag : CC
#	Use this flag to define compiler to use
CC = riscv32-unknown-elf-gcc
# Flag : LD
#	Use this flag to define compiler to use
LD = riscv32-unknown-elf-ld
# Flag : AS
#	Use this flag to define compiler to use
AS = riscv32-unknown-elf-as
# Flag : CFLAGS
#	Use this flag to define compiler options. Note, you can add compiler options from the command line using XCFLAGS="other flags"
PORT_CFLAGS = -g -march=$(RV_ISA) -mabi=ilp32 -static -mcmodel=medlow -mtune=sifive-3-series \
  -O3 -falign-functions=16 -funroll-all-loops \
	-finline-functions -falign-jumps=4 \
  -nostdlib -nostartfiles -ffreestanding -mstrict-align \
	-DTOTAL_DATA_SIZE=2000 -DMAIN_HAS_NOARGC=1 \
	-DPERFORMANCE_RUN=1

FLAGS_STR = "$(PORT_CFLAGS) $(XCFLAGS) $(XLFLAGS) $(LFLAGS_END)"
CFLAGS += $(PORT_CFLAGS) $(XCFLAGS) -I$(SIMPLE_SYSTEM_COMMON) -I$(PORT_DIR) -I.
#Flag : LFLAGS_END
#	Define any libraries needed for linking or other flags that should come at the end of the link line (e.g. linker scripts).
#	Note : On certain platforms, the default clock_gettime implementation is supported but requires linking of librt.
#SEPARATE_COMPILE=1
# Flag : SEPARATE_COMPILE
# You must also define below how to create an object file, and how to link.
OBJOUT 	= -o
LFLAGS 	=
ASFLAGS =
OFLAG 	= -o
COUT   	= -c

LFLAGS_END = -T $(LINKER_SCRIPT) -Xlinker -Map=$(OPATH)coremark.map -lm -lgcc
# Flag : PORT_SRCS
# 	Port specific source files can be added here
#	You may also need cvt.c if the fcvt functions are not provided as intrinsics by your compiler!
PORT_SRCS = $(PORT_DIR)/core_portme.c $(PORT_DIR)/ee_printf.c ./barebones/cvt.c $(CRT0) $(EXT_SRCS)
vpath %.c $(PORT_DIR)
vpath %.s $(PORT_DIR)

# Flag : LOAD
#	For a simple port, we assume self hosted compile and run, no load needed.

# Flag : RUN
#	For a simple port, we assume self hosted compile and run, simple invocation of the executable

LOAD = echo "Please set LOAD to the process of loading the executable to the flash"
RUN = echo "Please set LOAD to the process of running the executable (e.g. via jtag, or board reset)"

OEXT = .o
EXE = .elf

$(OPATH)$(PORT_DIR)/%$(OEXT) : %.c
	$(CC) $(CFLAGS) $(XCFLAGS) $(COUT) $< $(OBJOUT) $@

$(OPATH)%$(OEXT) : %.c
	$(CC) $(CFLAGS) $(XCFLAGS) $(COUT) $< $(OBJOUT) $@

$(OPATH)$(PORT_DIR)/%$(OEXT) : %.s
	$(AS) $(ASFLAGS) $< $(OBJOUT) $@

# Target : port_pre% and port_post%
# For the purpose of this simple port, no pre or post steps needed.

.PHONY : port_clean port_prebuild port_postbuild port_prerun port_postrun port_preload port_postload

port_postbuild:
	riscv32-unknown-elf-objdump -SD $(OPATH)coremark.elf > $(OPATH)coremark.dis
	riscv32-unknown-elf-objcopy -O binary $(OPATH)coremark.elf $(OPATH)coremark.bin
	srec_cat $(OPATH)coremark.bin -binary -offset 0x0000 -byte-swap 4 -o  $(OPATH)coremark.vmem -vmem


# FLAG : OPATH
# Path to the output folder. Default - current folder.
MKDIR = mkdir -p
