# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
#
# Simple tcl script for DC to do some wire-load-model-based sweep syntheses.

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

######################
##   DESIGN SETUP  ##
######################

set DUT "prim_prince"
# set DUT "prim_present"

lappend search_path "../../../ip/prim/rtl/"
set SRC {  "../../../ip/prim/rtl/prim_assert.sv" \
           "../../../ip/prim/rtl/prim_cipher_pkg.sv" \
           "../../../ip/prim/rtl/prim_present.sv" \
           "../../../ip/prim/rtl/prim_prince.sv" \
         }


# additional defines
set DEFINE ""

# additional parameters
set PARAMS ""

set CLK_PIN clk_i
set RST_PIN rst_ni

set TCK_SWEEP { 10.0 11.0 12.0 13.0 14.0 15.0 16.0 17.0 18.0 19.0 20.0 }
set IN_DEL  0.0
set OUT_DEL 0.0

###########################
##         SWEEP         ##
###########################

foreach TCK $TCK_SWEEP {
  ###########################
  ##   ELABORATE DESIGN    ##
  ###########################

  # delete previous designs.
  remove_design -designs
  sh rm -rf $WORKLIB/*

  analyze -define ${DEFINE} -format sv ${SRC}   > "${REPDIR}/${DUT}_${TCK}_analyze.rpt"
  elaborate  ${DUT} -parameters ${PARAMS}       > "${REPDIR}/${DUT}_${TCK}_elab.rpt"
  link                                          > "${REPDIR}/${DUT}_${TCK}_link.rpt"
  check_design                                  > "${REPDIR}/${DUT}_${TCK}_check.rpt"

  write_file -format ddc -hierarchy -output "${DDCDIR}/${DUT}_${TCK}_elab.ddc"
  write_file -format verilog -hierarchy -output "${DDCDIR}/${DUT}_${TCK}_elab.v"

  ###########################
  ##   APPLY CONSTRAINTS   ##
  ###########################

  # timing constraint in ns
  # set timing to 250 MHz
  set DELAY   ${TCK}

  create_clock ${CLK_PIN} -period ${TCK}

  set_ideal_network ${CLK_PIN}
  set_ideal_network ${RST_PIN}

  set_max_delay ${DELAY} -from [all_inputs] -to [all_outputs]
  set_input_delay ${IN_DEL} [remove_from_collection [all_inputs] {${CLK_PIN}}] -clock ${CLK_PIN}
  set_output_delay ${OUT_DEL}  [all_outputs] -clock ${CLK_PIN}

  set_driving_cell  -no_design_rule -lib_cell ${DRIVING_CELL} -pin X [all_inputs]
  set_load [load_of ${LOAD_LIB}/${LOAD_CELL}/A] [all_outputs]

  ######################
  ##    MAP DESIGN    ##
  ######################

  compile_ultra -gate_clock -scan  > "${REPDIR}/${DUT}_${TCK}_compile.rpt"

  #################
  ##   REPORTS   ##
  #################

  report_timing -nosplit               > "${REPDIR}/${DUT}_${TCK}_timing.rpt"
  report_area -hier -nosplit           > "${REPDIR}/${DUT}_${TCK}_area.rpt"
  report_constraints -all_violators    > "${REPDIR}/${DUT}_${TCK}_constraints.rpt"

  report_timing -nosplit -nworst 1000 -input -net -trans -cap > "${REPDIR}/${DUT}_${TCK}_timing_long.rpt"

  #################
  ##   NETLIST   ##
  #################

  change_names -rules verilog -hierarchy
  write_file -format ddc     -hierarchy -output "${DDCDIR}/${DUT}_${TCK}_mapped.ddc"
  write_file -format verilog -hierarchy -output "${VLOGDIR}/${DUT}_${TCK}_mapped.v"
}
