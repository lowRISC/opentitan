// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/silicon_creator/lib/boot_svc/boot_svc_enter_rescue.h"

#include "sw/device/silicon_creator/lib/error.h"

void boot_svc_enter_rescue_req_init(uint32_t skip_once,
                                    boot_svc_enter_rescue_req_t *msg) {
  msg->skip_once = skip_once;
  boot_svc_header_finalize(kBootSvcEnterRescueReqType,
                           sizeof(boot_svc_enter_rescue_req_t), &msg->header);
}

void boot_svc_enter_rescue_res_init(rom_error_t status,
                                    boot_svc_enter_rescue_res_t *msg) {
  msg->status = status;
  boot_svc_header_finalize(kBootSvcEnterRescueResType,
                           sizeof(boot_svc_enter_rescue_res_t), &msg->header);
}
