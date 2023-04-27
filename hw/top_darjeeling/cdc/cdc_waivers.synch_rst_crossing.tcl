# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
#
# Verix CDC waiver file

set_rule_status -rule {SYNCH_RST_CROSSING} -expression {(ResetSyncFlop =~ "top_earlgrey.*.u_sync_2.gen_generic.u_impl_generic.q_o*")} -status {Waived} -comment {REVIEW items : flops driven by reset synchronizers}
