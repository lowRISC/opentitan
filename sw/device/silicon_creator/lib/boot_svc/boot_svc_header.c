// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/silicon_creator/lib/boot_svc/boot_svc_header.h"

#include <stddef.h>

#include "sw/device/silicon_creator/lib/drivers/hmac.h"

void boot_svc_header_finalize(uint32_t type, uint32_t length,
                              boot_svc_header_t *header) {
  enum {
    kDigestRegionOffset = sizeof(header->digest),
  };
  static_assert(offsetof(boot_svc_header_t, digest) == 0,
                "`digest` must be the first field of `boot_svc_header_t`.");
  header->identifier = kBootSvcIdentifier;
  header->type = type;
  header->length = length;
  hmac_sha256((const char *)header + kDigestRegionOffset,
              length - kDigestRegionOffset, &header->digest);
}
