// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef _HANDLER_H_
#define _HANDLER_H_

typedef enum exc_id {
  kInstMisa = 0,
  kInstAccFault = 1,
  kInstIllegalFault = 2,
  kBkpt = 3,
  kLoadAccFault = 5,
  kStrAccFault = 7,
  kECall = 11,
  kIdMax = 31
} exc_id_t;

#endif
