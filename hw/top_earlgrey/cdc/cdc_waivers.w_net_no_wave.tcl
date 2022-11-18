# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
#
# Verix CDC waiver file

set_rule_status -rule {S_NET_NO_WAVE} -expression {(Signal =~ "ast_init_done[3:1]") && (DriverType =~ "Undriven") && (FanoutClockDomain == "IO_DIV4_CLK")} -status {Deferred} -comment {Deferred to Post-M2 while waiting for Nuvoton to clarify : https://github.com/lowRISC/opentitan/issues/16478}
set_rule_status -rule {S_NET_NO_WAVE} -expression {(Signal =~ "top_earlgrey.*.u_memory_2p*u_mem.gen_generic.u_impl_generic.*_rdata_o*")} -status {Waived} -comment {Signals from 2p memory}
