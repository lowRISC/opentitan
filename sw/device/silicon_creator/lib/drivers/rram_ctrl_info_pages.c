// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/silicon_creator/lib/drivers/rram_ctrl.h"

#define INFO_PAGE_STRUCT_DEF_(name_, page_id_, emulated_, num_pages_) \
  const rram_ctrl_info_page_t name_ = {                               \
      .page_id = (page_id_),                                          \
      .emulated = (emulated_),                                        \
      .num_pages = (num_pages_),                                      \
  };
RRAM_CTRL_INFO_PAGES_DEFINE(INFO_PAGE_STRUCT_DEF_);
#undef INFO_PAGE_STRUCT_DEF_
