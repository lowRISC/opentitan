// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/silicon_creator/lib/boot_svc/boot_svc_ownership_history.h"

#include "sw/device/lib/base/memory.h"
#include "sw/device/silicon_creator/lib/error.h"

void boot_svc_ownership_history_req_init(
    boot_svc_ownership_history_req_t *msg) {
  boot_svc_header_finalize(kBootSvcOwnershipHistoryReqType,
                           sizeof(boot_svc_ownership_history_req_t),
                           &msg->header);
}

void boot_svc_ownership_history_res_init(
    rom_error_t status, const uint32_t *history_digest,
    boot_svc_ownership_history_res_t *msg) {
  msg->status = status;
  memcpy(msg->history_digest, history_digest, sizeof(msg->history_digest));
  boot_svc_header_finalize(kBootSvcOwnershipHistoryResType,
                           sizeof(boot_svc_ownership_history_res_t),
                           &msg->header);
}
