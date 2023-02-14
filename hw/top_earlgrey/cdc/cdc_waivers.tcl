# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
#
# Verix CDC waiver file

# TODO: need to add more common waivers here. We may have to break this into
# multiple files.
#
# set_rule_status -rule { S_CONF_ENV } -status { Waived } -expression { } \
#   -comment {}
# set_rule_status -rule { S_CONF_ENV } -status { Waived } -all_rule_data \
#   -comment {}


# Assumes modules defined in run-cdc.tcl

if {[info exists modules] == 0} {
  error "modules variable does not exist!" 99
}

foreach mod $modules {
  if {[file exists $CDC_WAIVER_DIR/cdc_waivers.$mod.tcl]} {
    source $CDC_WAIVER_DIR/cdc_waivers.$mod.tcl
  }
}

# Addtional waivers based on category
source $CDC_WAIVER_DIR/cdc_waivers.w_masync.tcl
source $CDC_WAIVER_DIR/cdc_waivers.w_g_clk_glitch.tcl
source $CDC_WAIVER_DIR/cdc_waivers.w_async_rst_flops.tcl
source $CDC_WAIVER_DIR/cdc_waivers.w_recon.tcl
source $CDC_WAIVER_DIR/cdc_waivers.w_data.tcl
source $CDC_WAIVER_DIR/cdc_waivers.w_interface.tcl
source $CDC_WAIVER_DIR/cdc_waivers.w_fanout.tcl
source $CDC_WAIVER_DIR/cdc_waivers.w_net_no_wave.tcl
source $CDC_WAIVER_DIR/cdc_waivers.misc.tcl
source $CDC_WAIVER_DIR/cdc_waivers.data.tcl
source $CDC_WAIVER_DIR/cdc_waivers.multclk_crossings.tcl
source $CDC_WAIVER_DIR/cdc_waivers.synch_rst_crossing.tcl
source $CDC_WAIVER_DIR/cdc_waivers.rst_sync.tcl

# Common Waivers

# Muxed PAD output
# For IO PADs, Clock does not matter.
set_rule_status -rule {W_DATA W_MASYNC} -status {Waived} \
  -expression {(ReceivingFlop =~ "IO*")}                 \
  -comment {Direct output without flop}

# Driving from PAD to gpio/ uart/ i2c
set_rule_status -rule {W_MASYNC} -status {Waived}           \
  -expression {(Driver=~"IO*") &&                           \
    (ReceivingFlop=~"*u_gpio.gen_filter*prim_flop_2sync*")} \
  -comment {Other than PADS, other signals are static}
set_rule_status -rule {W_MASYNC} -status {Waived}                         \
  -expression {(Driver=~"IO*") && (ReceivingFlop=~"*u_uart*.*u_sync_1*")} \
  -comment {Other than PADS, other signals are static}
set_rule_status -rule {W_CNTL} -status {Waived}                           \
  -expression {(Signal=~"IO*") && (ReceivingFlop=~"*u_i2c*.*.u_sync_1*")} \
  -comment {PAD driving to I2C. PADs are not clock bounded}

set_rule_status -rule {W_GLITCH} -status {Waived}          \
  -expression {(GlitchInput=~"IO*") &&                     \
    (GlitchOutput=~"*u_sync_1*")} \
  -comment {Waive PADs input goes into synchronizer}

# AST signals reconverged
set_rule_status -rule {W_RECON_GROUPS} -status {Waived}                           \
  -expression {(ControlSignal =~ "u_ast.u_ast_clks_byp.*u_impl_generic.q_o*") && (ReconSignal=~"top_earlgrey.*.u_reg*")} \
  -comment {Reconverged signals coming from AST}

# W_GLITCH from unrecognized sync logics
set_rule_status -rule {W_GLITCH} -status {Waived}          \
  -expression {(GlitchOutput=~"*.u_sync_1.gen_generic.u_impl_generic.q_o*")} \
  -comment {Waive glitch paths that meet at and/or gates at the same clock but synchronization logics are not recognized}

set_rule_status -rule {W_RECON_GROUPS} -status {Waived}                           \
  -expression {(ControlSignal =~ "*u_pinmux_aon.u_reg.u_wkup_detector*cdc.u_src_to_dst_req*.u_sync1.*u_impl_generic.q_o*") && (ReconSignal=~"top_earlgrey.*.u_reg*")} \
  -comment {Reconverged signals coming from AST}

set_rule_status -rule {W_RECON_GROUPS} -status {Waived}                           \
  -expression {(ControlSignal =~ "*u_reg.*cdc*.prim_flop_2sync.u_sync_1.*u_impl_generic.q_o*") && (ReconSignal=~"top_earlgrey.*.u_reg*")} \
  -comment {Reconverged signals coming from AST}

# RV PLIC signals reconverged
set_rule_status -rule {W_RECON_GROUPS} -status {Waived}                           \
  -expression {(ControlSignal =~ "*u_rv_plic.*") && (ReconSignal=~"*u_rv_plic.u_gateway.ia*")} \
  -comment {Reconverged signals in RV PLIC}

# Misc RV PLIC signals reconverged
set_rule_status -rule {W_RECON_GROUPS} -status {Waived}                           \
  -expression {(ControlSignal =~ "*u_sync_1.gen_generic.u_impl_generic.q_o*") && (ReconSignal=~"*u_rv_plic.u_gateway.ia*")} \
  -comment {Reconverged signals in RV PLIC}

set_rule_status -rule {W_RECON_GROUPS} -status {Waived} -expression {(ReconSignal=~"top_earlgrey.u_xbar_main.u_asf_35.rspfifo.storage[0]*")} -comment {Intended reconvergence in xbar main}
set_rule_status -rule {W_RECON_GROUPS} -status {Waived} -expression {(ReconSignal=~"top_earlgrey.u_pwrmgr_aon.u_fsm.u_state_regs.u_state_flop.gen_generic.u_impl_generic.q_o*")} -comment {Intended reconvergence in pwrmgr fsm}
set_rule_status -rule {W_RECON_GROUPS} -status {Waived} -expression {(ControlSignal=~"top_earlgrey.u_xbar_main.u_asf_*.rs*fifo.sync_*ptr.u_sync_1.gen_generic.u_impl_generic.q_o*")} -comment {reconvergence caused by unrecognized qualification in async fifo}
set_rule_status -rule {W_RECON_GROUPS} -status {Waived} -expression {(ControlSignal=~"top_earlgrey.*.*sync*.*sync_1.gen_generic.u_impl_generic.q_o*")} -comment {reconvergence caused by unrecognized qualification in async fifo}
set_rule_status -rule {W_RECON_GROUPS} -status {Waived} -expression {(ControlSignal=~"top_earlgrey.*.*cdc*.*sync_1.gen_generic.u_impl_generic.q_o*")} -comment {reconvergence caused by unrecognized qualification in async fifo}


# PADs attribute to multiple IPs
# Assume the attributes are not used when IPs are active
set_rule_status -rule {W_FANOUT} -status {Waived}           \
  -expression {(Driver =~ "*u_pinmux_aon.dio_pad_attr_q*")} \
  -comment {ATTR static signal propagates into USB_CLK, AON_CLK. But no Reconvergence issue}

# SPI Device PADS output
set_rule_status -rule {W_DATA} -status {Waived} -expression             \
  {(MultiClockDomains =~ "*::SPI_DEV_CLK,SPI_DEV_PASSTHRU_CLK") &&      \
  (ReceivingFlop =~ "SPI_DEV_*")} -comment {Direct output without flop}
set_rule_status -rule {W_MASYNC} -status {Waived} -expression           \
  {(MultiClockDomains =~ "*::SPI_DEV_CLK,SPI_DEV_PASSTHRU_CLK") &&      \
  (ReceivingFlop =~ "SPI_DEV_*")} -comment {Direct output without flop}

set_rule_status -rule {W_DATA} -status {Waived} -expression               \
  {(MultiClockDomains =~ "*::SPI_HOST_CLK,SPI_HOST_PASSTHRU_CLK") &&      \
  (ReceivingFlop =~ "SPI_HOST_*")} -comment {Direct output without flop}
set_rule_status -rule {W_MASYNC} -status {Waived} -expression             \
  {(MultiClockDomains =~ "*::SPI_HOST_CLK,SPI_HOST_PASSTHRU_CLK") &&      \
  (ReceivingFlop =~ "SPI_HOST_*")} -comment {Direct output without flop}

## ASYNC FIFO Gray Pointer
set_rule_status -rule {W_CNTL} -status {Waived}                              \
  -expression {(Signal=~"*ptr_gray_q*") && (ReceivingFlop =~ "*.u_sync_1*")} \
  -comment {Gray Pointer sync}

## Waive pinmux attr: static
set_rule_status -rule {W_MASYNC} -status {Waived}        \
  -expression {(Driver=~"*u_pinmux_aon.dio_pad_attr_*")} \
  -comment {PAD Attributes are static signals.}

# JTAG en
set_rule_status -rule {W_ASYNC_RST_FLOPS} -status {Waived} \
  -expression {(DrivingSignal=~"*.u_pinmux_strap_sampling.tap_strap_q*")} \
  -comment {Tester should ensure no jtag transactions when tap_strap is sampled}

set_rule_status -rule {W_CNTL} -status {Waived} \
  -expression {(Signal=~"*u_pinmux_aon.dio_pad_attr_*")} \
  -comment {PAD Attributes are static signals.}
set_rule_status -rule {W_DATA} -status {Waived} \
  -expression {(Signal=~"*u_pinmux_aon.dio_pad_attr_*")} \
  -comment {PAD Attributes are static signals.}

set_rule_status -rule {S_GENCLK} -status {Waived} \
  -expression {(ClockTreeSignal=~"u_ast.u_ast_clks_byp.*") && (DrivenFlop =~ "u_ast.u_ast_clks_byp.*")} \
  -comment {ast clks are assumed to be checked by the partner as standalone.}

set_rule_status -rule {S_GENCLK} -status {Waived} \
  -expression {(ClockTreeSignal=~"IOC*") && (DrivenFlop =~ "u_ast.u_ast_clks_byp.*")} \
  -comment {ast clks are assumed to be checked by the partner as standalone.}

set_rule_status -rule {W_ASYNC_RST_FLOPS} -status {Waived} \
  -expression {(DrivingSignal=~"*.u_rstmgr_aon.*.u_rst_sync*.u_impl_generic.q_o*") && (ReceivingFlop =~ "*u_rstmgr_aon.*.gen_rst_chk.u_rst_chk.child_rst_asserted*")} \
  -comment {asynchronous reset generation in rstmgr}

set_rule_status -rule {W_INTERFACE} -status {Waived} -expression             \
  {(Signal=~"IO*") && \
  (ReceivingFlop=~ "top_earlgrey.u_spi_host1.u_spi_core.u_shift_reg.*_q*")} -comment {W_INTERFACE issues from PAD to spi_host}

set_rule_status -rule {W_INTERFACE} -status {Waived} -expression             \
  {(Signal=~"SPI_HOST*") && \
  (ReceivingFlop=~ "top_earlgrey.u_spi_host1.u_spi_core.u_shift_reg.*_q*")} -comment {W_INTERFACE issues from PAD to spi_host}

set_rule_status -rule {W_INTERFACE} -status {Waived} -expression             \
  {(Signal=~"top_earlgrey.*.u_reg.*.q*") && \
  (ReceivingFlop=~ "top_earlgrey.u_pinmux_aon.mio_out_retreg_q*")} -comment {W_INTERFACE issues from u_reg to pinmux}

set_rule_status -rule {W_INTERFACE} -status {Waived} -expression             \
  {(Signal=~"top_earlgrey.*.u_reg.*_q*") && \
  (ReceivingFlop=~ "top_earlgrey.u_pinmux_aon.mio_out_retreg_q*")} -comment {W_INTERFACE issues from u_reg to pinmux}

set_rule_status -rule {W_CNTL} -status {Waived}                           \
  -expression {(Signal=~"top_earlgrey.*.gen_generic.u_impl_generic.q_o*") && (ReceivingFlop=~"top_earlgrey.*.u_sync_1.gen_generic.u_impl_generic.q_o*")} \
  -comment {PAD driving to I2C. PADs are not clock bounded}

set_rule_status -rule {W_CNTL} -status {Waived}                           \
  -expression {(Signal=~"top_earlgrey.*.u_reg.*_cdc.u_src_to_dst_req.src_level") && (ReceivingFlop=~"top_earlgrey.*.u_sync_1.gen_generic.u_impl_generic.q_o*")} \
  -comment {PAD driving to I2C. PADs are not clock bounded}

set_rule_status -rule {W_CNTL} -status {Waived}                           \
  -expression {(Signal=~"top_earlgrey.*.u_reg.*_cdc.u_arb.*_sync.*.dst_ack_q") && (ReceivingFlop=~"top_earlgrey.*.u_sync_1.gen_generic.u_impl_generic.q_o*")} \
  -comment {PAD driving to I2C. PADs are not clock bounded}
