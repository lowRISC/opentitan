# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

# In the ping timer, there is a counter called u_prim_count_esc_cnt. The FSM that drives this uses
# the prim_count to count through the N_ESC_SEV senders and then clears it back to zero. As a
# result, it never tries to increment the counter at maximum value (N_ESC_SEV-1), so we will never
# see the precondition for the *CntIncrStable_A assertions. Waive the cover property for each
# assertion.
cover -disable -regexp ".*\.u_prim_count_esc_cnt\..*\.UpCntIncrStable_A:precondition1"
cover -disable -regexp ".*\.u_prim_count_esc_cnt\..*\.DnCntIncrStable_A:precondition1"

# In the ping timer, there is also a counter called u_prim_count_cnt. This counts down from the
# value supplied in ping_timeout_cyc_i (this happens to be constrained in
# alert_handler_ping_timer_assert_fpv.sv to be less than 8). When it gets to zero, we set the
# timer_expired flag, which disables the decrement. As such, we are never asked to decrement when
# equal to zero. Waive the cover property for each of the assertions that checks this.
cover -disable -regexp ".*\.u_prim_count_cnt\..*\.UpCntDecrStable_A:precondition1"
cover -disable -regexp ".*\.u_prim_count_cnt\..*\.DnCntDecrStable_A:precondition1"
