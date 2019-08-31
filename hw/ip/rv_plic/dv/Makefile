SIM_TOOL := irun

# Setting IP_NAME and PRJ_DIR. Assuming Makefile located at `hw/ip/<ip_name>/dv`
DV_DIR    := $(shell dirname $(realpath $(lastword $(MAKEFILE_LIST))))
IP_DIR    := $(subst /dv,,${DV_DIR})
wordslist := $(subst /, ,${IP_DIR})
IP_NAME   := $(lastword ${wordslist})
#IP_NAME  := $(word $(words ${wordslist}),${wordslist})

export PRJ_DIR:= $(realpath ${DV_DIR}/../../../..)

tests = riscv_plic_dir_test

rand:=$(shell awk 'BEGIN{srand();printf("%d", 65536*rand())}')

all: $(tests)

$(tests):
	irun -access +rwc +libext+.sv+ -svseed ${rand} -incdir ../rtl -incdir . -input probe.tcl -sv -f ${IP_NAME}.dv.f \
		-64bit \
		-top tb \
		-q -sv -uvm \
		-vlog_ext +.vh -I. \
		-uvmhome CDNS-1.2 \
		+timescale+1ns/1ns \
		+UVM_TESTNAME=$@
