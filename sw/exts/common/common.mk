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

all: $(LIB_DIR) $(OUTFILES)

.PHONY: $(LIB_DIR)

$(LIB_DIR):
	$(MAKE) -C $(LIB_DIR)

$(EXE).elf: $(OBJS) $(LINKER_SCRIPT) $(LIB_DIR)
	    $(CC) $(CFLAGS) $(OBJS) -T $(LINKER_SCRIPT) -o $@ $(LIBS) -Xlinker -Map=$(EXE).map

%.dis: %.elf
	$(OBJDUMP) -SD $^ > $@

# Note: this target requires the srecord package to be installed.
# XXX: This could be replaced by objcopy once
# https://sourceware.org/bugzilla/show_bug.cgi?id=19921
# is merged.
%.vmem: %.bin
	srec_cat $^ -binary -offset 0x0 -byte-swap 4 -o $@ -vmem

%.bin: %.elf
	$(OBJCOPY) -O binary $^ $@

%.o: %.c
	$(CC) $(CFLAGS) -MMD -c $(INCS) -o $@ $<

%.o: %.S
	$(CC) $(CFLAGS) -MMD -c $(INCS) -o $@ $<


-include $(DEPS)

clean:
	$(RM) -f *.o *.d *.bin *.elf *.vmem *.map *.dis $(GENHDRS)

distclean: clean
	cd $(LIB_DIR) && $(MAKE) distclean
	$(RM) -f $(OUTFILES) $(EXT_DIR)/*.o $(EXT_DIR)/*.d
