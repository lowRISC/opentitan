# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

# The UpCntIncrStable_A and DnCntIncrStable_A assertions are vacuous
# in this test because we can never get to the situation where the
# counter would saturate: it only be set to 1 and incremented, but it
# is reasonably wide (EscCntDw=32).
cover -disable -regexp ".*\.g_check_incr\.UpCntIncrStable_A:precondition1"
cover -disable -regexp ".*\.g_check_incr\.DnCntIncrStable_A:precondition1"
