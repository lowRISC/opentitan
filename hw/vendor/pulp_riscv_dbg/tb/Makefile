# Copyright 2019 Clifford Wolf
# Copyright 2019 Robert Balas
# Copyright 2020 ETH Zurich and University of Bologna.
# Permission to use, copy, modify, and/or distribute this software for any
# purpose with or without fee is hereby granted, provided that the above
# copyright notice and this permission notice appear in all copies.
#
# THE SOFTWARE IS PROVIDED "AS IS" AND THE AUTHOR DISCLAIMS ALL WARRANTIES WITH
# REGARD TO THIS SOFTWARE INCLUDING ALL IMPLIED WARRANTIES OF MERCHANTABILITY
# AND FITNESS. IN NO EVENT SHALL THE AUTHOR BE LIABLE FOR ANY SPECIAL, DIRECT,
# INDIRECT, OR CONSEQUENTIAL DAMAGES OR ANY DAMAGES WHATSOEVER RESULTING FROM
# LOSS OF USE, DATA OR PROFITS, WHETHER IN AN ACTION OF CONTRACT, NEGLIGENCE OR
# OTHER TORTIOUS ACTION, ARISING OUT OF OR IN CONNECTION WITH THE USE OR
# PERFORMANCE OF THIS SOFTWARE.

# Author: Robert Balas (balasr@iis.ee.ethz.ch)
# Description: All in one. Uses parts of picorv32's makefile.

MAKE			= make
CTAGS			= ctags

# vsim configuration
VVERSION                = "10.7b"

VLIB			= vlib-$(VVERSION)
VWORK			= work

VLOG			= vlog-$(VVERSION)
VLOG_FLAGS		= -pedanticerrors -suppress 2577 -suppress 2583
VLOG_LOG                = vloggy

VOPT			= vopt-$(VVERSION)
VOPT_FLAGS		= -debugdb -fsmdebug -pedanticerrors #=mnprft

VSIM			= vsim-$(VVERSION)
VSIM_HOME               = /usr/pack/modelsim-$(VVERSION)-kgf/questasim
VSIM_FLAGS              =  # user defined
ALL_VSIM_FLAGS		= $(VSIM_FLAGS) -sv_lib remote_bitbang/librbs_vsim
VSIM_DEBUG_FLAGS	= -debugdb
VSIM_GUI_FLAGS          = -gui -debugdb
VSIM_SCRIPT_BATCH       = vsim_batch.tcl
VSIM_SCRIPT_GUI         = vsim_gui.tcl

VCS                     = vcs-2017.03-kgf vcs
VCS_HOME                = /usr/pack/vcs-2017.03-kgf
VCS_FLAGS               =
SIMV_FLAGS              =

# verilator configuration
VERILATOR		= verilator
VERI_FLAGS              =
VERI_COMPILE_FLAGS      =
VERI_TRACE              =
VERI_DIR                = cobj_dir
VERI_CFLAGS             = -O2

# RTL source files
RTLSRC_TB_PKG		:=
RTLSRC_TB_TOP		:= tb_top.sv
RTLSRC_TB		:= boot_rom.sv \
				dp_ram.sv \
				mm_ram.sv \
				SimJTAG.sv \
				../sva/dm_top_sva.sv \
				../sva/dm_csrs_sva.sv \
				../sva/dm_sba_sva.sv \
				tb_test_env.sv \
				tb_top.sv

RTLSRC_VERI_TB          := boot_rom.sv \
				dp_ram.sv \
				mm_ram.sv \
				SimJTAG.sv \
				tb_top_verilator.sv

RTLSRC_INCDIR           := riscv/rtl/include

RTLSRC_FPNEW_PKG	:= fpnew/src/fpnew_pkg.sv
RTLSRC_RISCV_PKG	+= $(addprefix riscv/rtl/include/,\
				cv32e40p_apu_core_pkg.sv cv32e40p_pkg.sv \
				../../bhv/include/cv32e40p_tracer_pkg.sv)
RTLSRC_DM_PKG		+= ../src/dm_pkg.sv

RTLSRC_PKG 		= $(RTLSRC_FPNEW_PKG) dm_tb_pkg.sv $(RTLSRC_RISCV_PKG) $(RTLSRC_DM_PKG)
RTLSRC_RISCV		:= $(addprefix riscv/rtl/,\
				../bhv/cv32e40p_sim_clock_gate.sv \
				../bhv/cv32e40p_tracer.sv \
				cv32e40p_if_stage.sv \
				cv32e40p_cs_registers.sv \
				cv32e40p_register_file_ff.sv \
				cv32e40p_load_store_unit.sv \
				cv32e40p_id_stage.sv \
				cv32e40p_aligner.sv \
				cv32e40p_decoder.sv \
				cv32e40p_compressed_decoder.sv \
				cv32e40p_fifo.sv \
				cv32e40p_prefetch_buffer.sv \
				cv32e40p_hwloop_regs.sv \
				cv32e40p_mult.sv \
				cv32e40p_int_controller.sv \
				cv32e40p_ex_stage.sv \
				cv32e40p_alu_div.sv \
				cv32e40p_alu.sv \
				cv32e40p_ff_one.sv \
				cv32e40p_popcnt.sv \
				cv32e40p_apu_disp.sv \
				cv32e40p_controller.sv \
				cv32e40p_obi_interface.sv \
				cv32e40p_prefetch_controller.sv \
				cv32e40p_sleep_unit.sv \
				cv32e40p_core.sv)
RTLSRC_COMMON           := $(addprefix common_cells/src/,\
				cdc_2phase.sv fifo_v2.sv fifo_v3.sv\
				rstgen.sv rstgen_bypass.sv)
RTLSRC_TECH		:= $(addprefix tech_cells_generic/src/,\
				cluster_clock_inverter.sv pulp_clock_mux2.sv\
				cluster_clock_gating.sv)
RTLSRC_DEBUG            := ../debug_rom/debug_rom.sv
RTLSRC_DEBUG		+= $(addprefix ../src/,\
				dm_csrs.sv dmi_cdc.sv dmi_jtag.sv \
				dmi_jtag_tap.sv dm_mem.sv \
				dm_sba.sv dm_top.sv dm_obi_top.sv)

RTLSRC			+= $(RTLSRC_RISCV) $(RTLSRC_COMMON) $(RTLSRC_TECH) $(RTLSRC_DEBUG)

# versions for this tb
CV32E40P_SHA            = f9d63290eea738cb0a6fbf1e77bbd18555015a03
FPU_SHA                 = v0.6.1
COMMON_SHA              = 337f54a7cdfdad78b124cbdd2a627db3e0939141
TECH_SHA                = b35652608124b7ea813818b14a00ca76edd7599d

RAM_START_ADDR          = 0x1c000000

# TODO: clean this up
RTLSRC_VLOG_TB_TOP	:= $(basename $(notdir $(RTLSRC_TB_TOP)))
RTLSRC_VOPT_TB_TOP	:= $(addsuffix _vopt, $(RTLSRC_VLOG_TB_TOP))

# riscv bare metal cross compiling
RISCV			?= $(HOME)/.riscv
RV_CC			= $(RISCV)/bin/riscv32-unknown-elf-gcc
RV_CFLAGS		= -march=rv32imc -Os -g
RV_LDFLAGS		= -nostdlib -static -T prog/link.ld
RV_LDLIBS		= -lc -lm -lgcc
RV_OBJCOPY		= $(RISCV)/bin/riscv32-unknown-elf-objcopy

# assume verilator if no target chosen
.DEFAULT_GOAL := veri-run

all: veri-run

# vsim testbench compilation and optimization
vlib: .lib-rtl

.lib-rtl:
	$(VLIB) $(VWORK)
	touch .lib-rtl

# rebuild if we change some sourcefile
.build-rtl: .lib-rtl $(RTLSRC_PKG) $(RTLSRC) $(RTLSRC_TB_PKG) $(RTLSRC_TB)
	$(VLOG) -work $(VWORK) +incdir+$(RTLSRC_INCDIR) $(VLOG_FLAGS) \
	$(RTLSRC_PKG) $(RTLSRC) $(RTLSRC_TB_PKG) $(RTLSRC_TB)
	touch .build-rtl

vsim-all: .opt-rtl

.opt-rtl: .build-rtl
	$(VOPT) -work $(VWORK) $(VOPT_FLAGS) $(RTLSRC_VLOG_TB_TOP) -o \
	$(RTLSRC_VOPT_TB_TOP)
	touch .opt-rtl

# vcs testbench compilation

vcsify: $(RTLSRC_PKG) $(RTLSRC) $(RTLSRC_TB_PKG) $(RTLSRC_TB) remote_bitbang/librbs_vcs.so
	$(VCS) +vc -sverilog -race=all -ignore unique_checks -full64 \
		-timescale=1ns/1ps \
		-CC "-I$(VCS_HOME)/include -O3 -march=native" $(VCS_FLAGS) \
		$(RTLSRC_PKG) $(RTLSRC) $(RTLSRC_TB_PKG) $(RTLSRC_TB) \
		+incdir+$(RTLSRC_INCDIR)

vcs-clean:
	rm -rf simv* *.daidir *.vpd *.db csrc ucli.key vc_hdrs.h

# verilator testbench compilation

# We first test if the user wants to to vcd dumping. This hacky part is required
# because we need to conditionally compile the testbench (-DVCD_TRACE) and pass
# the --trace flags to the verilator call
ifeq ($(findstring +vcd,$(VERI_FLAGS)),+vcd)
VERI_TRACE="--trace"
VERI_CFLAGS+="-DVCD_TRACE"
endif
VPATH += ../
verilate: testbench_verilator

# We set the RUNPATH (not RPATH, allows LD_LIBRARY_PATH to overwrite) to
# remote_bitbang and manually link against librbs_veri since putting in
# librbs_veri.so as parameter doesn't work because it searches in the build
# directory
testbench_verilator: $(RTLSRC_VERI_TB) $(RTLSRC_PKG) $(RTLSRC) \
			remote_bitbang/librbs_veri.so
	$(VERILATOR) --cc --sv --exe $(VERI_TRACE) \
		--Wno-lint --Wno-UNOPTFLAT --Wno-BLKANDNBLK \
		--Wno-MODDUP +incdir+$(RTLSRC_INCDIR) --top-module \
		tb_top_verilator --Mdir $(VERI_DIR) \
		-CFLAGS "-std=gnu++11 $(VERI_CFLAGS)" $(VERI_COMPILE_FLAGS) \
		$(RTLSRC_PKG) $(RTLSRC_VERI_TB) $(RTLSRC) \
		-LDFLAGS "-L../remote_bitbang \
		-Wl,--enable-new-dtags -Wl,-rpath,remote_bitbang -lrbs_veri" \
		tb_top_verilator.cpp
	cd $(VERI_DIR) && $(MAKE) -f Vtb_top_verilator.mk
	cp $(VERI_DIR)/Vtb_top_verilator testbench_verilator

verilate-clean:
	if [ -d $(VERI_DIR) ]; then rm -r $(VERI_DIR); fi
	rm -rf testbench_verilator

# git dependencies
download_deps: fpnew/src/fpnew_pkg.sv $(RTLSRC_COMMON) $(RTLSRC_TECH) $(RTLSRC_RISCV)

fpnew/src/fpnew_pkg.sv:
	git clone https://github.com/pulp-platform/fpnew.git --recurse -b v0.6.1

$(RTLSRC_COMMON):
	git clone https://github.com/pulp-platform/common_cells.git
	cd common_cells/ && git checkout $(COMMON_SHA)

$(RTLSRC_TECH):
	git clone https://github.com/pulp-platform/tech_cells_generic.git
	cd tech_cells_generic/ && git checkout $(TECH_SHA)

$(RTLSRC_RISCV_PKG) $(RTLSRC_RISCV):
	git clone https://github.com/openhwgroup/cv32e40p.git riscv
	cd riscv/ && git checkout $(CV32E40P_SHA)

# openocd server
remote_bitbang/librbs_veri.so: INCLUDE_DIRS =./ $(VSIM_HOME)/include
remote_bitbang/librbs_veri.so:
	$(MAKE) -C remote_bitbang all
	mv remote_bitbang/librbs.so $@

remote_bitbang/librbs_vsim.so: INCLUDE_DIRS =./ $(VSIM_HOME)/include
remote_bitbang/librbs_vsim.so:
	$(MAKE) -C remote_bitbang all
	mv remote_bitbang/librbs.so $@

remote_bitbang/librbs_vcs.so: INCLUDE_DIRS =./ $(VCS_HOME)/include
remote_bitbang/librbs_vcs.so:
	$(MAKE) -C remote_bitbang all
	mv remote_bitbang/librbs.so $@

rbs-clean:
	$(MAKE) -C remote_bitbang clean
	rm -rf remote_bitbang/librbs_vsim.so remote_bitbang/librbs_vcs.so

# run tb and exit
.PHONY: vsim-tb-run
vsim-tb-run: ALL_VSIM_FLAGS += -c
vsim-tb-run: vsim-all remote_bitbang/librbs_vsim.so
	$(VSIM) -work $(VWORK) $(ALL_VSIM_FLAGS) \
	$(RTLSRC_VOPT_TB_TOP) -do 'source $(VSIM_SCRIPT_BATCH); exit -f'

# run tb and drop into interactive shell
.PHONY: vsim-tb-run-sh
vsim-tb-run: ALL_VSIM_FLAGS += -c
vsim-tb-run-sh: vsim-all remote_bitbang/librbs_vsim.so
	$(VSIM) -work $(VWORK) $(ALL_VSIM_FLAGS) \
	$(RTLSRC_VOPT_TB_TOP) -do $(VSIM_SCRIPT_BATCH)

# run tb with simulator gui
.PHONY: vsim-tb-run-gui
vsim-tb-run-gui: ALL_VSIM_FLAGS += $(VSIM_GUI_FLAGS)
vsim-tb-run-gui: vsim-all remote_bitbang/librbs_vsim.so
	$(VSIM) -work $(VWORK) $(ALL_VSIM_FLAGS) \
	$(RTLSRC_VOPT_TB_TOP) -do $(VSIM_SCRIPT_GUI)


.PHONY: vsim-clean
vsim-clean:
	if [ -d $(VWORK) ]; then rm -r $(VWORK); fi
	rm -f transcript vsim.wlf vsim.dbg trace_core*.log \
	.build-rtl .opt-rtl .lib-rtl *.vcd objdump

# compile and dump program
prog/test.elf: prog/test.c prog/crt0.S prog/syscalls.c prog/vectors.S
	$(RV_CC) $(RV_CFLAGS) $(RV_CPPFLAGS) $(RV_LDFLAGS) $^ $(RV_LDLIBS) -o $@

prog/test.hex: prog/test.elf
	$(RV_OBJCOPY) -O verilog --change-addresses -$(RAM_START_ADDR) $< $@

.PHONY: prog-clean
prog-clean:
	rm -vrf $(addprefix prog/,test.elf test.hex)

# run program
.PHONY: veri-run
veri-run: verilate prog/test.hex
	./testbench_verilator $(VERI_FLAGS) \
		"+firmware=prog/test.hex"

.PHONY: vsim-run
vsim-run: vsim-all prog/test.hex
vsim-run: ALL_VSIM_FLAGS += "+firmware=prog/test.hex"
vsim-run: vsim-tb-run

.PHONY: vsim-run-gui
vsim-run-gui: vsim-all prog/test.hex
vsim-run-gui: ALL_VSIM_FLAGS += "+firmware=prog/test.hex"
vsim-run-gui: vsim-tb-run-gui

.PHONY: vcs-run
vcs-run: vcsify prog/test.hex
	./simv -sv_lib remote_bitbang/librbs_vcs $(SIMV_FLAGS) "+firmware=prog/test.hex"

.PHONY: vcs-run-gui
vcs-run-gui: VCS_FLAGS+=-debug_all
vcs-run-gui: vcsify prog/test.hex
	./simv -sv_lib remote_bitbang/librbs_vcs $(SIMV_FLAGS) -gui "+firmware=prog/test.hex"

# general targets
.PHONY: clean
clean: vsim-clean verilate-clean vcs-clean rbs-clean prog-clean

.PHONY: distclean
distclean: clean
	rm -rf common_cells/ tech_cells_generic/ fpnew/ riscv/
