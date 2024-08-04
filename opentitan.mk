# Copyright (c) 2022 ETH Zurich and University of Bologna
# Copyright and related rights are licensed under the Solderpad Hardware
# License, Version 0.51 (the "License"); you may not use this file except in
# compliance with the License.  You may obtain a copy of the License at
# http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
# or agreed to in writing, software, hardware and materials distributed under
# this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
# CONDITIONS OF ANY KIND, either express or implied. See the License for the
# specific language governing permissions and limitations under the License.
#
#

GIT ?= git
BENDER ?= ./bender
VSIM ?= vsim
DPI-LIB ?= work-dpi
run_script := scripts/opentitan_start.tcl
SRAM ?= ""
BOOTMODE ?= 0
QUESTA = questa-2022.3-bt
IDMA_ROOT ?= $(shell $(BENDER) path idma)

dpi-library    ?= work-dpi

# Ensure half-built targets are purged
.DELETE_ON_ERROR:

# --------------
# RTL SIMULATION
# --------------

ifdef flash_preload
  VLOG_ARGS += +define+FLASH_PRELOAD
endif

ifdef jtag_sec_boot
  VLOG_ARGS += +define+JTAG_SEC_BOOT
endif

ifdef vip
compile_script := scripts/compile_opentitan_vip.tcl
else
compile_script := scripts/compile_opentitan.tcl
endif

VLOG_ARGS += -incr -64 -nologo -quiet -suppress vlog-2583 -suppress vlog-13314  +acc +nospecify +notimingchecks  -timescale \"1 ns / 1 ps\" 
XVLOG_ARGS += -64bit -compile -vtimescale 1ns/1ns -quiet +nospecify +notimingchecks

define generate_vsim
	echo 'set ROOT [file normalize [file dirname [info script]]/$3]' > $1
	$(BENDER) script $(VSIM) --vlog-arg="$(VLOG_ARGS)" $2 | grep -v "set ROOT" >> $1
	echo >> $1
endef

.PHONY: init build sim update clean secure_boot_jtag secure_boot_spi

build: $(dpi-library)/elfloader.so scripts/compile_opentitan.tcl scripts/compile_opentitan_vip.tcl $(OT_ROOT)/hw/tb/vips
	$(QUESTA) vsim -c -do 'source $(compile_script); quit'

sim: build
	$(QUESTA) vsim -do 'set SRAM $(SRAM); set BOOTMODE $(BOOTMODE); source $(run_script)'

update:
	$(BENDER) update

clean:
	rm -rf scripts/compile*
	rm -rf work
	rm -rf work-dpi
	rm -rf *.log
	rm -rf transcript
	rm -rf modelsim.ini
	rm -rf vsim.wlf
	rm -rf uart

scripts/compile_opentitan.tcl: Bender.yml
	$(call generate_vsim, $@, -t use_idma -t rtl -t test -t snitch_cluster ,..)

scripts/compile_opentitan_vip.tcl: Bender.yml
	$(call generate_vsim, $@, -t use_idma -t rtl -t test_ot_vip -t snitch_cluster, ..)

secure_boot_jtag:
	make clean sim BOOTMODE=0 SRAM=sw/tests/opentitan/flash_preload_hmac_smoketest/flash_preload_hmac_smoketest.elf jtag_sec_boot=1

secure_boot_spi:
	make clean sim BOOTMODE=1 vip=1

bender:
	wget "https://github.com/pulp-platform/bender/releases/download/v0.22.0/bender-0.22.0-x86_64-linux-gnu-centos7.8.2003.tar.gz"
	tar -xvzf bender-0.22.0-x86_64-linux-gnu-centos7.8.2003.tar.gz
	rm bender-0.22.0-x86_64-linux-gnu-centos7.8.2003.tar.gz
	$(BENDER) --version | grep -q "bender 0.22.0"

$(OT_ROOT)/hw/tb/vips:
	rm -rf $@
	mkdir $@
	rm -rf model_tmp && mkdir model_tmp
	cd model_tmp; wget https://www.infineon.com/dgdl/Infineon-S25fs256s-SimulationModels-v02_00-EN.zip?fileId=8ac78c8c7d0d8da4017d0f6251a24e7b
	cd model_tmp; mv 'Infineon-S25fs256s-SimulationModels-v02_00-EN.zip?fileId=8ac78c8c7d0d8da4017d0f6251a24e7b' model.zip
	cd model_tmp; unzip model.zip
	cd model_tmp; mv 'S25fs256s' exe_folder
	cd model_tmp/exe_folder; unzip S25fs256s.exe
	cp model_tmp/exe_folder/S25fs256s/model/s25fs256s.v model_tmp/exe_folder/S25fs256s/model/s25fs256s_verilog.sdf $@
	rm -rf model_tmp

init: bender update scripts/compile_opentitan.tcl scripts/compile_opentitan_vip.tcl $(OT_ROOT)/hw/tb/vips

# DPI
dpi := $(patsubst hw/tb/dpi/%.cc, ${dpi-library}/%.o, $(wildcard hw/tb/dpi/*.cc))


dpi_hdr := $(wildcard hw/tb/dpi/*.h)
dpi_hdr := $(addprefix $(root-dir), $(dpi_hdr))
CFLAGS := -I$(QUESTASIM_HOME)/include         \
          -I$(RISCV)/include                  \
          -std=c++11 -Ihw/tb/dpi -O3

$(dpi-library)/elfloader.o: $(dpi_hdr)
	mkdir -p $(dpi-library)
	$(CXX) -shared -fPIC -std=c++0x -Bsymbolic $(CFLAGS) -c  hw/tb/dpi/elfloader.cc -o $@

$(dpi-library)/elfloader.so: $(dpi)
	$(CXX) -shared -m64 -o $(dpi-library)/elfloader.so $? -L$(RISCV)/lib -Wl,-rpath,$(RISCV)/lib

