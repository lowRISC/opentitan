// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/silicon_creator/lib/boot_svc/boot_svc_empty.h"

void boot_svc_empty_init(boot_svc_empty_t *msg) {
  size_t i = 0, j = kBootSvcEmptyPayloadWordCount - 1;
  for (; launder32(i) < kBootSvcEmptyPayloadWordCount &&
         launder32(j) < kBootSvcEmptyPayloadWordCount;
       ++i, --j) {
    msg->payload[i] = 0;
  }
  HARDENED_CHECK_EQ(i, kBootSvcEmptyPayloadWordCount);
  HARDENED_CHECK_EQ(j, SIZE_MAX);
  boot_svc_header_finalize(kBootSvcEmptyType, sizeof(boot_svc_empty_t),
                           &msg->header);
}
