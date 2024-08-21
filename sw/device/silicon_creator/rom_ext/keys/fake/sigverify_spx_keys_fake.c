// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/silicon_creator/lib/sigverify/spx_key.h"
#include "sw/device/silicon_creator/rom_ext/keys/fake/rom_ext_test_spx_0_key.h"

// Just a single key presently, this could change later.
const sigverify_spx_key_t kSigverifySpxKey = ROM_EXT_TEST_KEY_0_SPX;
