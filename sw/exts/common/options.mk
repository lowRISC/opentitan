# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
#
##########################################################################
## The following variables must be set prior to invoking this Makefile  ##
## NAME        - Top level name of the final elf                        ##
## SRCS        - List of files to be compiled                           ##
## PROGRAM_DIR - Location of file corresponding to NAME                 ##
##########################################################################

PROGRAM_CFLAGS += -Wall -g -Os
ifeq ($(SIM),1)
  PROGRAM_CFLAGS += -DSIMULATION
endif

EXE           := $(NAME)
SW_DIR        := $(PROGRAM_DIR)/../..
LIB_DIR       := $(SW_DIR)/lib
LIB_NAME       = ot
EXT_DIR       := $(SW_DIR)/exts/common
EXT_SRCS      := $(EXT_DIR)/_crt.c
EXT_ASMS      :=
VENDOR_DIR    := $(SW_DIR)/vendor

RV_TOOLS      ?= /tools/riscv/bin/
OBJCOPY       ?= $(subst gcc,objcopy,$(wordlist 1,1,$(CC)))
OBJDUMP       ?= $(subst gcc,objdump,$(wordlist 1,1,$(CC)))

# ARCH = rv32im # to disable compressed instructions
ARCH           = rv32imc
LINKER_SCRIPT ?= $(EXT_DIR)/link.ld

REGTOOL        = ../../util/regtool.py

CC            := $(RV_TOOLS)/riscv32-unknown-elf-gcc
CFLAGS        ?= -Wall -g -Os -march=$(ARCH) -mabi=ilp32 -static -mcmodel=medany \
	         -fvisibility=hidden -nostdlib -nostartfiles $(PROGRAM_CFLAGS)

OBJS          := $(SRCS:.c=.o) $(EXT_SRCS:.c=.o) $(EXT_ASMS:.S=.o)
DEPS           = $(OBJS:%.o=%.d)

LIBS           =-L$(LIB_DIR) -l$(LIB_NAME)
INCS          +=-I$(LIB_DIR) -I$(VENDOR_DIR)

OUTFILES      := $(EXE).elf $(EXE).vmem $(EXE).bin $(EXE).dis $(EXE).map
