// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/coverage/smoke/target.h"

void covfunc_nested_hit(void) {}

void covfunc_hit(void) { covfunc_nested_hit(); }

void covfunc_nested_miss(void) {}

void covfunc_miss(void) { covfunc_nested_miss(); }
