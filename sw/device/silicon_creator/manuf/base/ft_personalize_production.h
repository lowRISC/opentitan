// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_SILICON_CREATOR_MANUF_BASE_FT_PERSONALIZE_PRODUCTION_H_
#define OPENTITAN_SW_DEVICE_SILICON_CREATOR_MANUF_BASE_FT_PERSONALIZE_PRODUCTION_H_

#include <stdbool.h>
#include <stdint.h>

// -----------------------------------------------------------------------------
// INDUSTRIAL-GRADE STRIP SWITCH: Bypassing Status-Recording and Filename
// Logging This strips the massive compile-time metadata block to keep size low,
// while leaving standard logging and UJSON handshakes perfectly operational!
// -----------------------------------------------------------------------------
#undef _RECORD_STATUS_CREATE
#define _RECORD_STATUS_CREATE(code_val, mod_id, file) ({})

#undef STATUS_REPORT_HERE
#define STATUS_REPORT_HERE(status) ({})

#endif  // OPENTITAN_SW_DEVICE_SILICON_CREATOR_MANUF_BASE_FT_PERSONALIZE_PRODUCTION_H_
