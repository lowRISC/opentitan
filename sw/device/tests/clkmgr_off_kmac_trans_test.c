// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// This tests that disabling the KMAC clock causes CSR accesses to it to fail.

#include "sw/device/tests/clkmgr_off_trans_impl.h"

bool test_main(void) { return execute_off_trans_test(kTestTransKmac); }
