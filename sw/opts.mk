# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
#
####################################################################################################
## SW build infrastructure - common opts                                                          ##
## Two types of embedded SW is built typically for a test - boot_rom and sw test application.     ##
## Each has two components - top level sources (indicated with SW_ prefix) and libraries          ##
## (indicated with LIB_ prefix.                                                                   ##
## If a new dir with SW or LIB sources are added, a 'srcs.mk' needs to be included and it should  ##
## specify the additional sources either via SW_SRCS or LIB_SRCS variable, See existing examples  ##
## for reference.                                                                                 ##
####################################################################################################

# sources and targets
SW_NAME       ?= $(notdir $(SW_DIR))
SW_SRCS       := $(CRT_SRCS) $(SW_SRCS)
SW_OBJS       += $(addprefix $(SW_BUILD_DIR)/, $(addsuffix .o, $(basename $(notdir $(SW_SRCS)))))
SW_DEPS       ?= lib
SW_BUILD_DIR  ?= $(SW_ROOT_DIR)/$(SW_DIR)

LIB_NAME      ?= ot
LIB_DIR       ?= $(SW_ROOT_DIR)/lib
LIB_TARGET    ?= $(LIB_BUILD_DIR)/lib${LIB_NAME}.a
LIB_SRCS      +=
LIB_OBJS      += $(addprefix $(LIB_BUILD_DIR)/, $(addsuffix .o, $(basename $(notdir $(LIB_SRCS)))))
LIB_BUILD_DIR ?= $(SW_BUILD_DIR)/lib

DEPS          += $(SW_OBJS:%.o=%.d) $(LIB_OBJS:%.o=%.d)
INCS          += -I$(SW_DIR) -I$(LIB_DIR) -I$(SW_BUILD_DIR) -I$(LIB_BUILD_DIR)

LINK_OPTS     += -T $(LINKER_OUTPUT)
LINK_OPTS     += $(SW_OBJS) -L$(LIB_BUILD_DIR) -l$(LIB_NAME)
LINK_OPTS     += -Xlinker -Map=${SW_BUILD_DIR}/${IMG_NAME}.map

# target (either 'boot_rom' or 'sw')
ifeq ($(SW_NAME),boot_rom)
  IMG_NAME    ?= rom
else
  IMG_NAME    ?= sw
endif

IMG_OUTPUTS       += $(SW_BUILD_DIR)/$(IMG_NAME).elf \
                     $(SW_BUILD_DIR)/$(IMG_NAME).map \
                     $(SW_BUILD_DIR)/$(IMG_NAME).dis \
                     $(SW_BUILD_DIR)/$(IMG_NAME).bin \
                     $(SW_BUILD_DIR)/$(IMG_NAME).vmem
GEN_HEADER_OUTPUTS = $(addprefix $(LIB_BUILD_DIR)/, $(GEN_HEADERS))
LINKER_OUTPUT     ?= $(addprefix $(LIB_BUILD_DIR)/, $(notdir $(LINKER_SCRIPT)))

# defaults
CRT_SRCS      ?= $(EXT_COMMON_DIR)/_crt.c
LINKER_SCRIPT ?= $(SW_ROOT_DIR)/exts/common/link.ld

# tools and opts
REGTOOL       ?= $(SW_ROOT_DIR)/../util/regtool.py
INFOTOOL      ?= $(SW_ROOT_DIR)/../util/rom_chip_info.py

RV_TOOLS      ?= /tools/riscv/bin
# ARCH = rv32im # to disable compressed instructions
ARCH           = rv32imc
CC             = ${RV_TOOLS}/riscv32-unknown-elf-gcc
CPP            = $(subst gcc,cpp,$(wordlist 1,1,$(CC)))
AR             = $(subst gcc,ar,$(wordlist 1,1,$(CC)))
AS             = $(subst gcc,as,$(wordlist 1,1,$(CC)))
LD             = $(subst gcc,ld,$(wordlist 1,1,$(CC)))
OBJCOPY        = $(subst gcc,objcopy,$(wordlist 1,1,$(CC)))
OBJDUMP        = $(subst gcc,objdump,$(wordlist 1,1,$(CC)))

CFLAGS        += -march=$(ARCH) -mabi=ilp32 -static -mcmodel=medany -Wall -g -Os \
                 -fvisibility=hidden -nostdlib -nostartfiles $(SW_FLAGS)
ARFLAGS        = rc
OBJCOPY_FLAGS +=

# conditional flags
SIM ?= 0
ifeq ($(SIM), 1)
  CFLAGS      += -DSIMULATION
endif

ifeq ($(TARGET), dv)
  MSG_FLOW         := elf
  CFLAGS           += -DDV_SIM
endif

ifeq ($(TARGET), fpga)
  CFLAGS      += -DFPGA_SIM
endif

# msg flow
MSG_FLOW  ?= uart
ifeq ($(MSG_FLOW), elf)
  CFLAGS           += -DMSG_FLOW=elf
  MSG_DATA_SECTION ?= msg_data
  MSG_DATA          = $(SW_BUILD_DIR)/$(MSG_DATA_SECTION).txt
  IMG_OUTPUTS      += $(MSG_DATA)
  OBJCOPY_FLAGS    += --remove-section=.$(MSG_DATA_SECTION)
endif
