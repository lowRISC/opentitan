// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/silicon_creator/lib/boot_svc/boot_svc_ownership_unlock.h"

#include "sw/device/lib/base/memory.h"
#include "sw/device/silicon_creator/lib/error.h"

void boot_svc_ownership_unlock_req_init(uint32_t unlock_mode, nonce_t nonce,
                                        const owner_key_t *next_owner_key,
                                        const owner_signature_t *signature,
                                        boot_svc_ownership_unlock_req_t *msg) {
  msg->unlock_mode = unlock_mode;
  memset(msg->reserved, 0, sizeof(msg->reserved));
  msg->nonce = nonce;
  msg->next_owner_key = *next_owner_key;
  msg->signature = *signature;
  boot_svc_header_finalize(kBootSvcOwnershipUnlockReqType,
                           sizeof(boot_svc_ownership_unlock_req_t),
                           &msg->header);
}

void boot_svc_ownership_unlock_res_init(rom_error_t status,
                                        boot_svc_ownership_unlock_res_t *msg) {
  msg->status = status;
  boot_svc_header_finalize(kBootSvcOwnershipUnlockResType,
                           sizeof(boot_svc_ownership_unlock_res_t),
                           &msg->header);
}
