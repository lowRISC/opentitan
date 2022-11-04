# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
#
# Meridian RDC Waivers

# Assumes modules defined in run-rdc.tcl
if {[info exists modules] == 0} {
  error "modules variable does not exist!" 99
}

foreach mod $modules {
  if {[file exists $RDC_WAIVER_DIR/rdc_waivers.$mod.tcl]} {
    source $RDC_WAIVER_DIR/rdc_waivers.$mod.tcl
  }
}

# clk_ast_ext_i: Ignore S_GENCLK
set_rule_status -rule {S_GENCLK} -status {Waived}  \
  -expression {(ClockTreeSignal=~"IOC6")} \
  -comment {External signal has SW bypass option. But usually not used. So internal generated clock is define ans main clock}

# RstMgrSwRst scenario does not involved in retention logic
set_rule_status -rule {E_RST_METASTABILITY} -status {Waived} \
  -expression {(FromScenario=="RstMgrSwRst") && \
    (MetaStableFlop=~"*u_pinmux_aon.*io_*_retreg*")} \
  -comment {RstMgrSwRst scenario does not involved in retention logic}

# RstMgrSwRst scenario: Xbar should not have any outstanding req.
set_rule_status -rule {E_RST_METASTABILITY} -status {Waived} \
  -expression {(FromScenario=="RstMgrSwRst") && \
    (ResetFlop=~"*.u_reg_if.outstanding_q")} \
  -comment {RstMgrSwRst scenario: Xbar should not have any outstanding req.}
