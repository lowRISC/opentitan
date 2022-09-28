# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
#
# Meridian RDC Waivers for SPI_DEVICE
#

# W_RST_COMBO_LOGIC
# rst_rx/txfifo signals are reset signals but also returns data to SW. it is
# recognized as combo reset by tool but reset line is OK.
# TODO: Add buffer to separate other logics from reset
set_rule_status -rule {W_RST_COMBO_LOGIC} -status {Waived}  \
  -expression {(SourceReset=~"*.u_spi_device.u_reg.u_control_rst_*xfifo.q*")} \
  -comment {rst_rx,txfifo are reset signals directly connected to the registers.q}

set_rule_status -rule {W_RST_COMBO_LOGIC} -status {Waived} \
  -expression {(SourceReset=~"*.u_spi_device.rst_*_buf")}  \
  -comment {rst csb, tpm_csb are reset merging with scan chain.}
