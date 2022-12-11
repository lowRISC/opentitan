GIT ?= git
BENDER ?= bender
VSIM ?= vsim
DPI-LIB ?= work-dpi


ifdef exclude_otp_rom
	VLOG_ARGS += +define+EXCLUDE_OTP_ROM
	questa-cmd += +define+EXCLUDE_OTP_ROM
endif

all: sim_all 

clean: sim_clean

# Ensure half-built targets are purged
.DELETE_ON_ERROR:

# --------------
# RTL SIMULATION
# --------------

VLOG_ARGS += -suppress vlog-2583 -suppress vlog-13314 -suppress vlog-13198 -suppress vlog-7033 +nospecify +define+ +notimingchecks  -suppress vopt-13276 -suppress vlog-13233 -timescale \"1 ns / 1 ps\" 
XVLOG_ARGS += -64bit -compile -vtimescale 1ns/1ns -quiet +nospecify +notimingchecks

define generate_vsim
	echo 'set ROOT [file normalize [file dirname [info script]]/$3]' > $1
	bender script $(VSIM) --vlog-arg="$(VLOG_ARGS)" $2 | grep -v "set ROOT" >> $1
	echo >> $1
	#echo 'vlog "$$ROOT/test/elfloader.cpp" -ccflags "-std=c++11"' >> $1 # TODO: Reactivate elf loader later?
endef

sim_all: scripts/compile.tcl

sim_clean:
	rm -rf scripts/compile.tcl
	rm -rf scripts/work

scripts/compile.tcl: Bender.yml
	$(call generate_vsim, $@, -t rtl -t test,..)
