GIT ?= git
BENDER ?= bender
VSIM ?= vsim
DPI-LIB ?= work-dpi
compile_script := compile.tcl
compile_script_preload := compile_preload.tcl
run_script := start.tcl
run_script_preload := start_preload.tcl
SRAM ?= ""
# Ensure half-built targets are purged
.DELETE_ON_ERROR:

# --------------
# RTL SIMULATION
# --------------

ifdef flash_preload
  VLOG_ARGS += +define+FLASH_PRELOAD
endif
ifdef secure
  VLOG_ARGS += +define+SECURE
endif

# -suppress vlog-13198 -suppress vlog-7033 -suppress vopt-13276 -suppress vlog-13233

VLOG_ARGS += -incr -64 -nologo -quiet -suppress vlog-2583 -suppress vlog-13314  +nospecify +notimingchecks  -timescale \"1 ns / 1 ps\" 
XVLOG_ARGS += -64bit -compile -vtimescale 1ns/1ns -quiet +nospecify +notimingchecks

define generate_vsim
	echo 'set ROOT [file normalize [file dirname [info script]]/$3]' > $1
	bender script $(VSIM) --vlog-arg="$(VLOG_ARGS)" $2 | grep -v "set ROOT" >> $1
	echo >> $1
endef

build: compile.tcl
	vsim -c -do 'source $(compile_script); quit'

run: build
	vsim -do 'set SRAM ${SRAM}; source $(run_script)'

sim: build run

update:
	bender update

clean:
	rm -rf compile.tcl
	rm -rf work
	rm -rf *.log
	rm -rf transcript
	rm -rf modelsim.ini
	rm -rf vsim.wlf
	rm -rf uart

compile.tcl: ../Bender.yml
	$(call generate_vsim, $@, -t rtl -t test,..)

