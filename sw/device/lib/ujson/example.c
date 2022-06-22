// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

/////////////////////////////////////////////////////////////////////////////
// The corresponding C file to a `ujson` header file should simply define
// the preprocessor token `UJSON_SERDE_IMPL` and then include the header
// file.  This will cause the preprocessor to emit the `serialize` and
// `deserialize` implementations for the data structures.
#define UJSON_SERDE_IMPL
#include "sw/device/lib/ujson/example.h"
