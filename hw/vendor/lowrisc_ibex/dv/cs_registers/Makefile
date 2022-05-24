# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

TOOL     = verilator

SO_NAME  = reg_dpi.so

BUILDDIR = build
SRCEXT   = cc
OBJDIR   = $(BUILDDIR)/obj
BINDIR   = $(BUILDDIR)/bin

SRCS    := $(shell find . -name '*.$(SRCEXT)' ! -path './tb/*' ! -path './build/*')
SRCDIRS := $(shell find . -name '*.$(SRCEXT)' ! -name 'tb*' ! -name 'build*' -exec dirname {} \; | uniq)
OBJS    := $(patsubst %.$(SRCEXT),$(OBJDIR)/%.o,$(SRCS))

DEBUG    = -g
INCLUDES = -I./env -I./rst_driver -I./reg_driver -I./model
CFLAGS   = -std=c++14 -m64 -fPIC -Wall -pedantic $(DEBUG) $(INCLUDES)
LDFLAGS  = -shared

CC       = $(CXX)

# Add svdpi include
TOOLDIR = $(subst bin/$(TOOL),,$(shell which $(TOOL)))
ifeq ($(TOOL),vcs)
  INCLUDES += -I$(TOOLDIR)include
else
  INCLUDES += -I$(TOOLDIR)share/verilator/include/vltstd
endif

.PHONY: all clean

all: build

build: $(BINDIR)/$(SO_NAME)
	@echo "Build done"

$(BINDIR)/$(SO_NAME): buildrepo $(OBJS)
	@mkdir -p `dirname $@`
	@echo "Linking $@..."
	@$(CC) $(OBJS) $(LDFLAGS) -o $@

$(OBJDIR)/%.o: %.$(SRCEXT)
	@echo "Generating dependencies for $<..."
	@$(call make-depend,$<,$@,$(subst .o,.d,$@))
	@echo "Compiling $<..."
	@$(CC) $(CFLAGS) -c $< -o $@

clean:
	$(RM) -r $(BUILDDIR)

buildrepo:
	@$(call make-repo)

define make-repo
   for dir in $(SRCDIRS); \
   do \
	mkdir -p $(OBJDIR)/$$dir; \
   done
endef


# usage: $(call make-depend,source-file,object-file,depend-file)
define make-depend
  $(CC) -MM       \
        -MF $3    \
        -MP       \
        -MT $2    \
        $(CFLAGS) \
        $1
endef

