// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef REGISTER_TYPES_H_
#define REGISTER_TYPES_H_

struct CSRParams {
  bool PMPEnable;
  unsigned int PMPGranularity;
  unsigned int PMPNumRegions;
  unsigned int MHPMCounterNum;
  unsigned int MHPMCounterWidth;
};

#endif  // REGISTER_TYPES_H_
