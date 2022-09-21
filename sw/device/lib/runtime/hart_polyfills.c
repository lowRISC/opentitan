// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#define _DEFAULT_SOURCE  // Make sure we get usleep() from unistd.h.

#include <stddef.h>
#include <unistd.h>

#include "sw/device/lib/runtime/hart.h"

void busy_spin_micros(uint32_t usec) { usleep(usec); }

// Because this function is defined by libc as well, we do not bother
// defining abort() on-target.
//
// noreturn void abort(void);

// `extern` declarations to give the inline functions in the
// corresponding header a link location.

extern void wait_for_interrupt(void);
extern void icache_invalidate(void);
