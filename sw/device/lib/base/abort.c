// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/base/abort.h"

NO_RETURN void abort() __attribute__((alias("base_abort")));
NO_RETURN void base_abort(void) {
	__builtin_abort();
}