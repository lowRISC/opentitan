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

# USBDEV Wake up to PINMUX
set_rule_status -rule {E_RST_METASTABILITY} -status {Waived} \
  -expression {(ResetFlop=~"*.u_usbdev.u_reg.u_wake_control_cdc.u_src_to_dst_req.dst_level_q") && \
    (MetaStableFlop=~"*.u_pinmux_aon.u_usbdev_aon_wake.wake_detect_active_q")} \
  -comment {Suspend request signal is a pulse signal. \
    It is to initiate the wakeup detector FSM inside pinmux. \
    When Power is down, the state machine is already configures.}

# USBDEV SW RST REQ: All reset are in phase (sync assert, sync de-assert)
set_rule_status -rule {E_RST_METASTABILITY} -status {Waived} \
  -expression {(FromScenario=="RstMgrSwRst") && \
    (ResetFlop=~"*.u_usbdev.gen_no_stubbed_*") && \
    (MetaStableFlop=~"*.u_xbar_main.u_asf_41.*.fifo_*ptr*") && \
    (ClockDomains=="USB_CLK::USB_CLK")} \
  -comment {SW Reset is sync assert and sync de-assert. \
    So, when signal crossing the domain, it has no metastability issue.}
