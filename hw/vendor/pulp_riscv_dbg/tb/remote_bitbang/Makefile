# Copyright (C) 2020 ETH Zurich and University of Bologna
#
# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# You may obtain a copy of the License at
#
#     http://www.apache.org/licenses/LICENSE-2.0
#
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# See the License for the specific language governing permissions and
# limitations under the License.
#
#
# Author: Robert Balas (balasr@iis.ee.ethz.ch)

CFLAGS          = -Wall -Wextra -Wno-missing-field-initializers \
			-Wno-unused-function -Wno-missing-braces \
			-O2 -g -march=native \
			-DENABLE_LOGGING -DNDEBUG
CFLAGS_DBG      =
# we need gnu11 and no-strict-aliasing
ALL_CFLAGS      = -std=gnu11 -fno-strict-aliasing $(CFLAGS)
ALL_CFLAGS_DBG  = -std=gnu11 -Wall -Wextra -Wno-missing-field-initializers \
			-Wno-unused-function -Wno-missing-braces \
			-O0 -g -fno-strict-aliasing \
			-fsanitize=address -fno-omit-frame-pointer \
			-DENABLE_LOGGING -DENABLE_DEBUG $(CFLAGS_DBG)\
# -fsanitize=undefined \
# -fsanitize=leak \


# TODO: better path?
LIB_DIRS        =
LIBS            =
INCLUDE_DIRS    = ./


LDFLAGS         = $(addprefix -L, $(LIB_DIRS))
LDLIBS          = $(addprefix -l, $(LIBS))

SRCS            = remote_bitbang.c sim_jtag.c
OBJS            = $(SRCS:.c=.o)
INCLUDES        = $(addprefix -I, $(INCLUDE_DIRS))

HEADERS         = $(wildcard *.h)

# libs
SV_LIB          = librbs.so

# header file dependency generation
DEPDIR          := .d
DEPDIRS         := $(addsuffix /$(DEPDIR),.)
# goal: make gcc put a dependency file called obj.Td (derived from subdir/obj.o)
# in subdir/.d/
DEPFLAGS        = -MT $@ -MMD -MP -MF $(@D)/$(DEPDIR)/$(patsubst %.o,%.Td,$(@F))
# move gcc generated header dependencies to DEPDIR
# this rename step is here to make the header dependency generation "atomic"
POSTCOMPILE     = @mv -f $(@D)/$(DEPDIR)/$(patsubst %.o,%.Td,$(@F)) \
			$(@D)/$(DEPDIR)/$(patsubst %.o,%.d,$(@F)) && touch $@

# GNU recommendations for install targets
prefix          = /usr/local
exec_prefix     = $(prefix)
bindir          = $(exec_prefix)/bin
libdir          = $(exec_prefix)/lib
includedir      = $(prefix)/include

INSTALL         = install
INSTALL_PROGRAM = $(INSTALL)
INSTALL_DATA    = ${INSTALL} -m 644

CTAGS           = ctags

# compilation targets
all: sv-lib

debug: ALL_CFLAGS = $(ALL_CFLAGS_DBG)
debug: all

sv-lib: ALL_CFLAGS += -fPIC
sv-lib: $(SV_LIB)

#compilation boilerplate
$(SV_LIB): $(OBJS)
	$(LD) -shared -E --exclude-libs ALL -o $(SV_LIB) $(LDFLAGS) \
		$(OBJS) $(LDLIBS)

# $@ = name of target
# $< = first dependency
%.o: %.c
%.o: %.c $(DEPDIR)/%.d $(DEPDIRS)
	$(CC) $(DEPFLAGS) $(ALL_CFLAGS) $(INCLUDES) $(LDFLAGS) \
		-c $(CPPFLAGS) $< -o $@ $(LDLIBS)
	$(POSTCOMPILE)

# check if we need to create the dependencies folders (gcc doesn't)
$(DEPDIRS):
	$(shell mkdir -p $(DEPDIRS) > /dev/null)
# make won't fail if the dependency file doesn't exist
$(addsuffix /$(DEPDIR)/%.d,. main benchmark test dpi): ;

# prevent automatic deletion as intermediate file
.PRECIOUS: $(addsuffix /$(DEPDIR)/%.d,. main benchmark test dpi)

# emacs tag generation
.PHONY: TAGS
TAGS:
	$(CTAGS) -R -e -h=".c.h" --tag-relative=always \
		. $(LIB_DIRS) $(INCLUDE_DIRS) $(BINUTILS_PATH)/bfd

# TODO: missing install targets
# cleanup
.PHONY: clean
clean:
	rm -rf $(SV_LIB) $(OBJS) $(DEPDIRS)

.PHONY: distclean
distclean: clean
	rm -f TAGS

# include auto generated header dependency information
include $(wildcard $(addsuffix /*.d,$(DEPDIRS)))
