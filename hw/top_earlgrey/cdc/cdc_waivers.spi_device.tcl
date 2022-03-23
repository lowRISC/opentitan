# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
#
# Verix CDC waiver file
# Expression:
#  ControlSignal==""
#  ReconSignal==""
#  MultiClockDomains=="IO_DIV2_CLK::IO_DIV4_CLK"

set_rule_status -rule {W_RECON_GROUPS} -status {Waived}         \
   -expression {(ControlSignal=~"*u_status_23_to_1_sync.*") &&       \
                (ReconSignal=~"*u_spid_status.outclk_p2s_byte_*")} \
   -comment {status bits are converged into SPI line. But transmit bit-by-bit. OK to send old and new status bits in a transaction}
