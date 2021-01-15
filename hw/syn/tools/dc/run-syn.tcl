# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
#
# Simple tcl script for DC to do some wire-load-model-based test syntheses.

#####################
##  PREPARE FLOW   ##
#####################

set syn_root ""
if {[info exists ::env(syn_root)]} {
  set syn_root "$::env(syn_root)"
} else {
  puts "ERROR: Script run without syn_root environment variable."
  quit
}

set foundry_root ""
if {[info exists ::env(foundry_root)]} {
  set foundry_root "$::env(foundry_root)"
} else {
  puts "ERROR: Script run without foundry_root environment variable."
  quit
}

# Tool setup.
# TODO: The below path assumes a certain directory structure in the foundry
# area which does not exist in the open repo.
source "${foundry_root}/syn/dc/setup.tcl"

# if in interactive mode, do not exit at the end of the script
if { [info exists ::env(INTERACTIVE)] } {
  set RUN_INTERACTIVE 1
} else {
  set RUN_INTERACTIVE 0
}

# path to directory containing the source list file
set SV_FLIST $::env(SV_FLIST)
set BUILD_DIR $::env(BUILD_DIR)

# just compile the "core" toplevel at the moment
# might want to switch to top_earlgrey_asic later on (with pads)
set DUT $::env(DUT)
set CONSTRAINT $::env(CONSTRAINT)

# paths
set WORKLIB  "${BUILD_DIR}/WORK"
set REPDIR   "${BUILD_DIR}/REPORTS"
set DDCDIR   "${BUILD_DIR}/DDC"
set RESULTDIR "${BUILD_DIR}/results"
set VLOGDIR  "${BUILD_DIR}/NETLISTS"

exec mkdir -p ${REPDIR} ${DDCDIR} ${VLOGDIR} ${WORKLIB} ${RESULTDIR}

# define work lib path
define_design_lib WORK -path $WORKLIB

#######################
## CONFIGURATIONS   ###
#######################

# Define the verification setup file for Formality
set_svf ${RESULTDIR}/${DUT}.svf

# Setup SAIF Name Mapping Database
saif_map -start

###The following variable helps verification when there are differences between DC and FM while inferring logical hierarchies
set_app_var hdlin_enable_hier_map true

#######################
##  DESIGN SOURCES  ###
#######################

# this PRIM_DEFAULT_IMPL selects the appropriate technology by defining
# PRIM_DEFAULT_IMPL=prim_pkg::Impl<tech identifier>
# PRIM_DEFAULT_IMPL is set inside the library setup script
set DEFINE "PRIM_DEFAULT_IMPL=${PRIM_DEFAULT_IMPL}+${PRIM_STD_CELL_VARIANT}"

# additional parameters
set PARAMS "KmacEnMasking=1"

###########################
##   ELABORATE DESIGN    ##
###########################

# delete previous designs.
remove_design -designs
sh rm -rf $WORKLIB/*

analyze -vcs "-sverilog +define+${DEFINE} -f ${SV_FLIST}" > "${REPDIR}/analyze.rpt"
elaborate  ${DUT} -parameters ${PARAMS}                   > "${REPDIR}/elab.rpt"
link                                                      > "${REPDIR}/link.rpt"
check_design                                              > "${REPDIR}/check.rpt"

set_verification_top

write_file -format ddc -hierarchy -output "${DDCDIR}/elab.ddc"
#write_file -format verilog -hierarchy -output "${DDCDIR}/elab.v"

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

puts "Applying constraints for ${DUT}"
source "${CONSTRAINT}"
puts "Done applying constraints for ${DUT}"

# If hold time should be fixed
# set_fix_hold ${CLK_PIN}

######################
##    MAP DESIGN    ##
######################

# TODO: we may have to disable a couple of optimizations in order
# to prevent the tool from optimizing away dummy logic or logic from blocks
# that are only half-finished

# preserve hierarchy for reports
compile_ultra -gate_clock -scan -no_autoungroup > "${REPDIR}/compile.rpt"

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

#################
##   NETLIST   ##
#################

change_names -rules verilog -hierarchy
define_name_rules fixbackslashes -allowed "A-Za-z0-9_" -first_restricted "\\" -remove_chars
change_names -rule fixbackslashes -h
write_file -format ddc     -hierarchy -output "${DDCDIR}/mapped.ddc"
write_file -format verilog -hierarchy -output "${VLOGDIR}/mapped.v"

# Write final SDC
write_sdc -nosplit ${RESULTDIR}/${DUT}.final.sdc
# If SAIF is used, write out SAIF name mapping file for PrimeTime-PX
saif_map -type ptpx -write_map ${RESULTDIR}/${DUT}.mapped.SAIF.namemap
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
