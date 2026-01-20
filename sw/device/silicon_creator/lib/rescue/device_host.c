// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include <stdint.h>

// Supply UART NCO constants for linking as host code.
const uint32_t kUartBaud115K = 1;
const uint32_t kUartBaud230K = 2;
const uint32_t kUartBaud460K = 3;
const uint32_t kUartBaud921K = 4;
const uint32_t kUartBaud1M33 = 5;
const uint32_t kUartBaud1M50 = 6;
