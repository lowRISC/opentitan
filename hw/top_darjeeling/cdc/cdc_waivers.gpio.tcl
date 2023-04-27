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
   -expression {(ControlSignal=~"*u_gpio.gen_filter*") &&       \
                (ReconSignal=~"*u_gpio.u_reg.u_intr_state.q*")} \
   -comment {filters are converged into the interrupt status registers. Each bit is independent}
