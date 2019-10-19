#File : core_portme.mak

include ${SW_ROOT_DIR}/opts.mk

PORT_CLEAN  := $(IMG_OUTPUTS)

# FLAG : EXE, OEXT
# Extensions of generated outputs
OEXT = .o
EXE  = .elf

# FLAG : OPATH
# Path to the output folder. Default - current folder.
OPATH = $(SW_BUILD_DIR)/

# Flag : OUTFLAG
# Use this flag to define how to to get an executable (e.g -o)
OUTFLAG = $(LINK_OPTS) -o

# Flag : CFLAGS
# Use this flag to define compiler options. Note, you can add compiler options
# from the command line using XCFLAGS="other flags"
PORT_CFLAGS  = -DTOTAL_DATA_SIZE=6000 -DMAIN_HAS_NOARGC=1
FLAGS_STR    = "$(PORT_CFLAGS) $(XCFLAGS) $(XLFLAGS) $(LFLAGS_END)"
CFLAGS      += $(PORT_CFLAGS) $(XCFLAGS) -I$(PORT_DIR) -I. $(INCS)

# Flag : LFLAGS_END
# Define any libraries needed for linking or other flags that should come
# at the end of the link line (e.g. linker scripts).
# Note : On certain platforms, the default clock_gettime implementation
# is supported but requires linking of librt.
LFLAGS_END =

# Flag : SEPARATE_COMPILE
# Do compile and link steps separately. Not needed at this point.

# You must also define below how to create an object file, and how to link.
OBJOUT  = -o
LFLAGS  =
ASFLAGS =
OFLAG   = -o
COUT    = -c

# Flag : PORT_SRCS
# Port specific source files can be added here
# You may also need cvt.c if the fcvt functions are not provided as intrinsics by your compiler!
PORT_SRCS = $(PORT_DIR)/core_portme.c $(PORT_DIR)/ee_printf.c $(EXT_SRCS)
vpath %.c $(PORT_DIR)
vpath %.s $(PORT_DIR)

# Flag : LOAD
# For a simple port, we assume self hosted compile and run, no load needed.

# Flag : RUN
# For a simple port, we assume self hosted compile and run, simple invocation of the executable

# Flag : MKDIR
MKDIR = mkdir -p

LOAD = echo "Please set LOAD to the process of loading the executable to the flash"
RUN = echo "Please set LOAD to the process of running the executable (e.g. via jtag, or board reset)"

$(OPATH)%$(OEXT) : %.c
	$(CC) $(CFLAGS) $(XCFLAGS) $(COUT) $< $(OBJOUT) $@

$(OPATH)%$(OEXT) : %.s
	$(AS) $(ASFLAGS) $< $(OBJOUT) $@

$(OPATH)%$(OEXT) : $(PORT_DIR)/%.c
	$(CC) $(CFLAGS) $(XCFLAGS) $(COUT) $< $(OBJOUT) $@

$(OPATH)%$(OEXT) : $(PORT_DIR)/%.s
	$(AS) $(ASFLAGS) $< $(OBJOUT) $@

%.vmem: %.bin
	srec_cat $^ -binary -offset 0x0 -byte-swap 4 -o $@ -vmem

%.bin: %.elf
	$(OBJCOPY) -O binary $^ $@

%.dis: %.elf
	$(OBJDUMP) -SD $^ > $@

$(SW_BUILD_DIR)/$(IMG_NAME).elf: $(OUTFILE)
	$(MAKE) $(OUTFILE)
	mv $(OUTFILE) $@

# Target : port_pre% and port_post%

.PHONY : port_clean port_prebuild port_postbuild port_prerun port_postrun port_preload port_postload
