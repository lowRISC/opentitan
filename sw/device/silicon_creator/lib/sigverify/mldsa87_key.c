// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/silicon_creator/lib/sigverify/mldsa87_key.h"

const uint8_t kSigverifyMldsa87ImageContext[] = {
    'O', 'T', '-', 'M', 'L', 'D', 'S', 'A', '-', 'I', 'M', 'A', 'G', 'E',
};
const size_t kSigverifyMldsa87ImageContextSize =
    sizeof(kSigverifyMldsa87ImageContext);
