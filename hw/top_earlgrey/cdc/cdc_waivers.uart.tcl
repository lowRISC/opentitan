# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
#
# Verix CDC waiver file
# Expression:
#  ControlSignal==""
#  ReconSignal==""
#  MultiClockDomains=="IO_DIV2_CLK::IO_DIV4_CLK"

# PATH violation to PINMUX
set_rule_status -status {Waived} -rule {W_DATA} \
  -expression {(Signal=~"*u_uart_core.tx_out_q*") && (ReceivingFlop=~"IO*")} \
  -comment {Pinmux is clock invariant}

set_rule_status -status {Waived} -rule {W_MASYNC} \
  -expression {(Driver=~"*u_uart_core.tx_out_q*") && (ReceivingFlop=~"IO*")} \
  -comment {Pinmux is clock invariant}
