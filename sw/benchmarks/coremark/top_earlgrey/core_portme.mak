#File : core_portme.mak

NAME         = coremark
PORTME_DIR  := $(shell dirname $(realpath $(lastword $(MAKEFILE_LIST))))
PROGRAM_DIR := $(PORTME_DIR)/../

include ${PROGRAM_DIR}/../../exts/common/options.mk
PORT_CLEAN  := $(OUTFILES)


# Flag : OUTFLAG
#	Use this flag to define how to to get an executable (e.g -o)
OUTFLAG= -T $(LINKER_SCRIPT) -L$(LIB_DIR) -l$(LIB_NAME) -Xlinker -Map=coremark.map -o
# Flag : CC
#	Use this flag to define compiler to use
CC 		= $(RV_TOOLS)/riscv32-unknown-elf-gcc
# Flag : LD
#	Use this flag to define compiler to use
LD		= $(RV_TOOLS)/riscv32-unknown-elf-ld
# Flag : AS
#	Use this flag to define compiler to use
AS		= $(RV_TOOLS)/riscv32-unknown-elf-as
# Flag : CFLAGS
#	Use this flag to define compiler options. Note, you can add compiler options from the command line using XCFLAGS="other flags"
PORT_CFLAGS = -DTOTAL_DATA_SIZE=6000 -DMAIN_HAS_NOARGC=1
FLAGS_STR = "$(PORT_CFLAGS) $(XCFLAGS) $(XLFLAGS) $(LFLAGS_END)"
CFLAGS += $(PORT_CFLAGS) $(XCFLAGS) -I$(PORT_DIR) -I. -I$(LIB_DIR)
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
COUT 	= -c

LFLAGS_END =
# Flag : PORT_SRCS
# 	Port specific source files can be added here
#	You may also need cvt.c if the fcvt functions are not provided as intrinsics by your compiler!
PORT_SRCS = $(PORT_DIR)/core_portme.c $(PORT_DIR)/ee_printf.c $(EXT_SRCS)
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
	$(RV_TOOLS)/riscv32-unknown-elf-objcopy -O binary coremark.elf coremark.bin
	srec_cat coremark.bin -binary -offset 0x0 -byte-swap 4 -o coremark.vmem -vmem
	$(RV_TOOLS)/riscv32-unknown-elf-objdump -SD coremark.elf > coremark.dis

# FLAG : OPATH
# Path to the output folder. Default - current folder.
OPATH = ./
MKDIR = mkdir -p
