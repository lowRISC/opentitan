// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// See pinmux_config.h for the explaination of this include ordering.
#include "sw/device/lib/testing/json/pinmux.h"
#undef UJSON_SERDE_IMPL
#define UJSON_SERDE_IMPL 1
#include "sw/device/lib/testing/json/pinmux_config.h"
