// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/silicon_creator/lib/boot_svc/boot_svc_next_boot_bl0_slot.h"

#include "sw/device/silicon_creator/lib/error.h"

void boot_svc_next_boot_bl0_slot_req_init(
    uint32_t next_slot, boot_svc_next_boot_bl0_slot_req_t *msg) {
  msg->next_bl0_slot = next_slot;
  boot_svc_header_finalize(kBootSvcNextBl0SlotReqType,
                           sizeof(boot_svc_next_boot_bl0_slot_req_t),
                           &msg->header);
}

void boot_svc_next_boot_bl0_slot_res_init(
    rom_error_t status, boot_svc_next_boot_bl0_slot_res_t *msg) {
  msg->status = status;
  boot_svc_header_finalize(kBootSvcNextBl0SlotResType,
                           sizeof(boot_svc_next_boot_bl0_slot_res_t),
                           &msg->header);
}
