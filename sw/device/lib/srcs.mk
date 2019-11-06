# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

LIB_DIR           ?= $(SW_ROOT_DIR)/device/lib
INCS              += -I$(LIB_DIR)

GEN_HEADERS       += $(LIB_LOC_DIF_SRCS:.c=_regs.h)
LIB_LOC_DIF_SRCS  += uart.c gpio.c spi_device.c flash_ctrl.c hmac.c usbdev.c rv_timer.c pinmux.c
LIB_LOC_EXT_SRCS  += usb_controlep.c usb_simpleserial.c irq.c handler.c print_log.c irq_vectors.S memcpy.c

LIB_SRCS          += $(addprefix $(LIB_DIR)/, $(LIB_LOC_DIF_SRCS) $(LIB_LOC_EXT_SRCS))
