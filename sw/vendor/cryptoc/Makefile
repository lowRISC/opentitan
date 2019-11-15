# Copyright 2016 The Chromium OS Authors. All rights reserved.
# Use of this source code is governed by a BSD-style license that can be
# found in the LICENSE file.

obj ?= ./build
CROSS_COMPILE ?=
CC ?= $(CROSS_COMPILE)gcc
AR ?= $(CROSS_COMPILE)ar

SOURCES = hmac.c
SOURCES += p256.c
SOURCES += p256_ec.c
SOURCES += p256_ecdsa.c
SOURCES += p256_prng.c
SOURCES += sha.c
SOURCES += sha256.c
ifeq ($(CONFIG_UPTO_SHA512),y)
SOURCES += sha384.c
SOURCES += sha512.c
endif
SOURCES += util.c

# Use V=1 for verbose output
ifeq ($(V),)
Q := @
else
Q :=
endif

CFLAGS += -Iinclude
CFLAGS += -Wall -Werror
CFLAGS += -DTHIRD_PARTY
ifeq ($(CONFIG_UPTO_SHA512),y)
CFLAGS += -DSHA512_SUPPORT
endif

OBJS := $(patsubst %.c,$(obj)/%.o,$(SOURCES))
DEPS := $(patsubst %.c,$(obj)/%.d,$(SOURCES))

# This is the default target
$(obj)/libcryptoc.a: $(OBJS)
	@echo "  AR      $(notdir $@)"
	$(Q)$(AR) scr $@ $^

# Special target which allows to trigger re-compiling of all sources without
# linking a library.
objs: $(OBJS)

$(obj):
	@echo "  MKDIR   $(obj)"
	$(Q)mkdir -p $(obj)

$(obj)/%.d $(obj)/%.o: %.c | $(obj)
	@echo "  CC      $(notdir $<)"
	$(Q)$(CC) $(CFLAGS) -c -MMD -MF $(basename $@).d -o $(basename $@).o $<

.PHONY: clean
clean:
	@echo "  RM      $(obj)"
	$(Q)rm -rf $(obj)

ifneq ($(MAKECMDGOALS),clean)
-include $(DEPS)
endif
