// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/silicon_creator/lib/boot_svc/boot_svc_ownership_activate.h"

#include "sw/device/lib/base/memory.h"
#include "sw/device/silicon_creator/lib/error.h"

void boot_svc_ownership_activate_req_init(
    uint32_t primary_bl0_slot, uint32_t erase_previous, nonce_t nonce,
    const owner_signature_t *signature,
    boot_svc_ownership_activate_req_t *msg) {
  msg->primary_bl0_slot = primary_bl0_slot;
  msg->erase_previous = erase_previous;
  memset(msg->reserved, 0, sizeof(msg->reserved));
  msg->nonce = nonce;
  msg->signature = *signature;
  boot_svc_header_finalize(kBootSvcOwnershipActivateReqType,
                           sizeof(boot_svc_ownership_activate_req_t),
                           &msg->header);
}

void boot_svc_ownership_activate_res_init(
    rom_error_t status, boot_svc_ownership_activate_res_t *msg) {
  msg->status = status;
  boot_svc_header_finalize(kBootSvcOwnershipActivateResType,
                           sizeof(boot_svc_ownership_activate_res_t),
                           &msg->header);
}
