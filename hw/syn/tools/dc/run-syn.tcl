# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
#
# Simple tcl script for DC to do some wire-load-model-based test syntheses.

#####################
##  PREPARE FLOW   ##
#####################

proc get_env_var {name} {
  if {[info exists ::env($name)]} {
    set val "[set ::env([set name])]"
    puts "::env($name) = $val"
    return $val
  } else {
    puts "ERROR: Script run without $name environment variable."
    quit
  }
}

set FOUNDRY_ROOT       [get_env_var "FOUNDRY_ROOT"]
set SYN_ROOT           [get_env_var "SYN_ROOT"]
set SV_FLIST           [get_env_var "SV_FLIST"]
set BUILD_DIR          [get_env_var "BUILD_DIR"]
set DUT                [get_env_var "DUT"]
set CONSTRAINT         [get_env_var "CONSTRAINT"]
set FOUNDRY_CONSTRAINT [get_env_var "FOUNDRY_CONSTRAINT"]
set PARAMS             [get_env_var "PARAMS"]
set POST_ELAB_SCRIPT   [get_env_var "POST_ELAB_SCRIPT"]
set TERMINATION_STAGE  [get_env_var "TERMINATION_STAGE"]

# This is not a CDC run.
set IS_CDC_RUN 0

# if in interactive mode, do not exit at the end of the script
if { [info exists ::env(INTERACTIVE)] } {
  set RUN_INTERACTIVE 1
} else {
  set RUN_INTERACTIVE 0
}

# paths
set WORKLIB  "${BUILD_DIR}/WORK"
set REPDIR   "${BUILD_DIR}/REPORTS"
set DDCDIR   "${BUILD_DIR}/DDC"
set RESULTDIR "${BUILD_DIR}/results"
set VLOGDIR  "${BUILD_DIR}/NETLISTS"

exec mkdir -p ${REPDIR} ${DDCDIR} ${VLOGDIR} ${WORKLIB} ${RESULTDIR}

# define work lib path
define_design_lib WORK -path $WORKLIB

########################
## Library Setup      ##
########################

if {$FOUNDRY_ROOT != ""} {
  # ASIC lib setup for DC.
  source "${FOUNDRY_ROOT}/syn/dc/setup.tcl"
  # this PRIM_DEFAULT_IMPL selects the appropriate technology by defining
  # PRIM_DEFAULT_IMPL=prim_pkg::Impl<tech identifier>
  # PRIM_DEFAULT_IMPL is set inside the library setup script
  set DEFINE "PRIM_DEFAULT_IMPL=${PRIM_DEFAULT_IMPL}+${PRIM_STD_CELL_VARIANT}"
} else {
  # GTECH lib setup for DC.
  source "${SYN_ROOT}/tools/dc/gtech-setup.tcl"
  # This black-boxes the 1p and 2p memory models (used for GTECH runs only).
  set DEFINE "SYNTHESIS_MEMORY_BLACK_BOXING=TRUE"
}

#######################
## CONFIGURATIONS   ###
#######################

# Define the verification setup file for Formality
set_svf ${RESULTDIR}/${DUT}.svf

# Setup SAIF Name Mapping Database
saif_map -start

###The following variable helps verification when there are differences between DC and FM while inferring logical hierarchies
set_app_var hdlin_enable_hier_map true

###########################
##   Env var file        ##
###########################

set fp [open "${BUILD_DIR}/env_variables.tcl" w+]
puts $fp "set ::env(INTERACTIVE) 1"
puts $fp "set ::env(SYN_ROOT) $SYN_ROOT"
puts $fp "set ::env(FOUNDRY_ROOT) $FOUNDRY_ROOT"
puts $fp "set ::env(PARAMS) $PARAMS"
puts $fp "set ::env(SV_FLIST) $SV_FLIST"
puts $fp "set ::env(BUILD_DIR) $BUILD_DIR"
puts $fp "set ::env(DUT) $DUT"
puts $fp "set ::env(CONSTRAINT) $CONSTRAINT"
puts $fp "set ::env(FOUNDRY_CONSTRAINT) $FOUNDRY_CONSTRAINT"
puts $fp "set ::env(POST_ELAB_SCRIPT) $POST_ELAB_SCRIPT"
close $fp

###########################
##   ELABORATE DESIGN    ##
###########################

# delete previous designs.
remove_design -designs
sh rm -rf $WORKLIB/*

analyze -vcs "-sverilog +define+${DEFINE} -f ${SV_FLIST}" > "${REPDIR}/analyze.rpt"
if { $TERMINATION_STAGE == "analyze" } { exit }
elaborate  ${DUT} -parameters ${PARAMS}                   > "${REPDIR}/elab.rpt"
link                                                      > "${REPDIR}/link.rpt"
check_design                                              > "${REPDIR}/check.rpt"

set_verification_top

if {$POST_ELAB_SCRIPT != ""} {
  source ${POST_ELAB_SCRIPT}
}

write_file -format ddc -hierarchy -output "${DDCDIR}/elab.ddc"

if { $TERMINATION_STAGE == "elab" } { exit }

#############################
##   CLOCK GATING SETUP    ##
#############################

# be more specific if defaults do not suffice
# set_clock_gating_style -num_stages 1                   \
#                        -positive_edge_logic integrated \
#                        -control_point before           \
#                        -control_signal scan_enable

###########################
##   APPLY CONSTRAINTS   ##
###########################

if {$CONSTRAINT != ""} {
  puts "Applying constraints for ${DUT}"
  source "${CONSTRAINT}"
  puts "Done applying constraints for ${DUT}"
}

if {$FOUNDRY_CONSTRAINT != ""} {
  puts "Applying foundry constraints for ${DUT}"
  source "${FOUNDRY_CONSTRAINT}"
  puts "Done applying foundry constraints for ${DUT}"
}

# If hold time should be fixed
# set_fix_hold ${CLK_PIN}

######################
##    MAP DESIGN    ##
######################

# only use compile_ultra if the foundry library is defined.
# otherwise we can only do a compile with gtech cells.
if {$FOUNDRY_ROOT == ""} {
  # enable auto ungrouping and boundary optimization for
  # gtech experiments, in order to approximate actual
  # implementation runs with compile_ultra.
  compile -gate_clock             \
          -scan                   \
          -boundary_optimization  \
          -auto_ungroup area      > "${REPDIR}/compile.rpt"
} else {
  # preserve hierarchy for reports
  compile_ultra -gate_clock \
                -scan       \
                -no_autoungroup > "${REPDIR}/compile.rpt"
}

#################
##   NETLIST   ##
#################

change_names -rules verilog -hierarchy
define_name_rules fixbackslashes -allowed "A-Za-z0-9_" -first_restricted "\\" -remove_chars
change_names -rule fixbackslashes -h

# Change the name in case the netlist has not been mapped against a real ASIC lib.
if {$FOUNDRY_ROOT == ""} {
  set NETLIST_NAME "mapped_gtech"
} else {
  set NETLIST_NAME "mapped"
}

write_file -format ddc     -hierarchy -output "${DDCDIR}/${NETLIST_NAME}.ddc"
write_file -format verilog -hierarchy -output "${VLOGDIR}/${NETLIST_NAME}.v"

# Write final SDC
write_sdc -nosplit ${RESULTDIR}/${DUT}.final.sdc
# If SAIF is used, write out SAIF name mapping file for PrimeTime-PX
saif_map -type ptpx -write_map ${RESULTDIR}/${DUT}.${NETLIST_NAME}.SAIF.namemap

if { $TERMINATION_STAGE == "compile" } { exit }

#################
##   REPORTS   ##
#################

# write NAND2 equivalent to file for the reporting scripts
sh echo ${NAND2_GATE_EQUIVALENT} > "${REPDIR}/gate_equiv.rpt"

report_clocks                                 > "${REPDIR}/clocks.rpt"
report_clock -groups                          > "${REPDIR}/clock.groups.rpt"
report_path_group                             > "${REPDIR}/path_group.rpt"
report_clock_gating -multi_stage -nosplit     > "${REPDIR}/clock_gating.rpt"
report_timing -nosplit -slack_lesser_than 0.0 > "${REPDIR}/timing.rpt"
report_area   -hier -nosplit                  > "${REPDIR}/area.rpt"
report_power  -hier -nosplit                  > "${REPDIR}/power.rpt"
report_constraints -all_violators             > "${REPDIR}/constraints.rpt"

report_timing      -nosplit -nworst 1000 -input -net -trans -cap > "${REPDIR}/timing_long.rpt"

# ##############################
# ##  INCREMENTAL FLATTENING  ##
# ##############################

# compile_ultra -inc

# #################
# ##   REPORTS   ##
# #################

# report_timing      -nosplit -nworst 100 > "${REPDIR}/flat_timing.rpt"
# report_timing      -nosplit -nworst 1000 -input -net -trans -cap > "${REPDIR}/flat_timing_long.rpt"
# report_area  -hier -nosplit             > "${REPDIR}/flat_area.rpt"
# report_power -hier -nosplit             > "${REPDIR}/flat_power.rpt"
# report_constraints -all_violators       > "${REPDIR}/flat_constraints.rpt"

# #################
# ##   NETLIST   ##
# #################

# write_file -format ddc     -hierarchy -output "${DDCDIR}/flat.ddc"
# write_file -format verilog -hierarchy -output "${VLOGDIR}/flat.v"

if { $RUN_INTERACTIVE == 0 } {
  exit
}
