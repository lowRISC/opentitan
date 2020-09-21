# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
#
# Simple tcl script for DC to do some wire-load-model-based test syntheses.

#####################
##  PREPARE FLOW   ##
#####################

# tool setup
set CONFIG_PATH "../../../foundry/syn/dc/"
source ${CONFIG_PATH}/setup.tcl

# paths
set WORKLIB  "WORK"
set REPDIR   "REPORTS"
set DDCDIR   "DDC"
set VLOGDIR  "NETLISTS"

exec mkdir -p ${REPDIR} ${DDCDIR} ${VLOGDIR} ${WORKLIB}

# define work lib path
define_design_lib WORK -path $WORKLIB

#######################
##  DESIGN SOURCES  ###
#######################

set DUT "otp_ctrl_lfsr_timer"

lappend search_path "../../../ip/prim/rtl/"
set SRC {  "../../../ip/prim/rtl/prim_util_pkg.sv"           \
           "../../../ip/prim/rtl/prim_assert.sv"             \
           "../../../ip/prim/rtl/prim_lfsr.sv"               \
           "../../../ip/otp_ctrl/rtl/otp_ctrl_reg_pkg.sv"    \
           "../../../ip/otp_ctrl/rtl/otp_ctrl_pkg.sv"        \
           "../../../ip/otp_ctrl/rtl/otp_ctrl_lfsr_timer.sv" }

# additional defines
set DEFINE ""

# additional parameters
set PARAMS ""

###########################
##   ELABORATE DESIGN    ##
###########################

# delete previous designs.
remove_design -designs
sh rm -rf $WORKLIB/*

analyze -define ${DEFINE} -format sv ${SRC}    > "${REPDIR}/${DUT}_analyze.rpt"
elaborate  ${DUT} -parameters ${PARAMS}        > "${REPDIR}/${DUT}_elab.rpt"
link                                           > "${REPDIR}/${DUT}_link.rpt"
check_design                                   > "${REPDIR}/${DUT}_check.rpt"

write_file -format ddc -hierarchy -output "${DDCDIR}/${DUT}_elab.ddc"

###########################
##   APPLY CONSTRAINTS   ##
###########################

set CLK_PIN clk_i
set RST_PIN rst_ni

# timing constraint in ns
# set timing to 250 MHz
set TCK     4.0
set IN_DEL  1.0
set OUT_DEL 1.0
set DELAY   ${TCK}

create_clock ${CLK_PIN} -period ${TCK}

set_ideal_network ${CLK_PIN}
set_ideal_network ${RST_PIN}

set_max_delay ${DELAY} -from [all_inputs] -to [all_outputs]
set_input_delay ${IN_DEL} [remove_from_collection [all_inputs] {${CLK_PIN}}] -clock ${CLK_PIN}
set_output_delay ${OUT_DEL}  [all_outputs] -clock ${CLK_PIN}

# attach load and drivers to IOs to get a more realistic estimate
set_driving_cell  -no_design_rule -lib_cell ${DRIVING_CELL} -pin ${DRIVING_CELL_PIN} [all_inputs]
set_load [load_of ${LOAD_CELL_LIB}/${LOAD_CELL}/${LOAD_CELL_PIN}] [all_outputs]


# set a nonzero critical range to be able to spot the violating paths better
# in the report
# set_critical_range 0.2 ${DUT}

######################
##    MAP DESIGN    ##
######################

compile_ultra -gate_clock -scan > "${REPDIR}/${DUT}_compile.rpt"

# preserve hierarchy for reports
#compile_ultra -gate_clock -scan -no_autoungroup > "${REPDIR}/${DUT}_compile.rpt"

#################
##   REPORTS   ##
#################

report_clocks                                 > "${REPDIR}/${DUT}_clocks.rpt"
report_timing -nosplit -slack_lesser_than 0.0 > "${REPDIR}/${DUT}_timing.rpt"
report_area   -hier -nosplit                  > "${REPDIR}/${DUT}_area.rpt"
report_power  -hier -nosplit                  > "${REPDIR}/${DUT}_power.rpt"
report_constraints -all_violators             > "${REPDIR}/${DUT}_constraints.rpt"

report_timing      -nosplit -nworst 1000 -input -net -trans -cap > "${REPDIR}/${DUT}_timing_long.rpt"

#################
##   NETLIST   ##
#################

change_names -rules verilog -hierarchy
write_file -format ddc     -hierarchy -output "${DDCDIR}/${DUT}_mapped.ddc"
write_file -format verilog -hierarchy -output "${VLOGDIR}/${DUT}_mapped.v"
