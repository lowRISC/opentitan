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
