# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
#
# Verix CDC waiver file
# Expression:
#  ControlSignal==""
#  ReconSignal==""
#  MultiClockDomains=="IO_DIV2_CLK::IO_DIV4_CLK"
#


# LC escalate output to multiple peripherals
set_rule_status -rule {W_FANOUT} -status {Waived} \
  -expression {(Driver =~ "*u_lc_ctrl*.u_prim_lc_sender_escalate_en*")} \
  -comment {No Reconvergence issue. Each IP handles Escalate En individually}
