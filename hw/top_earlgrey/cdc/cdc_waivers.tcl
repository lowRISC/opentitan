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
