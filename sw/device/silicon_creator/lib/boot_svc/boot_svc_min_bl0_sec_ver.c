// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/silicon_creator/lib/boot_svc/boot_svc_min_bl0_sec_ver.h"

#include "sw/device/silicon_creator/lib/error.h"

void boot_svc_min_bl0_sec_ver_req_init(uint32_t min_sec_version,
                                       boot_svc_min_bl0_sec_ver_req_t *msg) {
  msg->min_bl0_sec_ver = min_sec_version;
  boot_svc_header_finalize(kBootSvcMinBl0SecVerReqType,
                           sizeof(boot_svc_min_bl0_sec_ver_req_t),
                           &msg->header);
}

void boot_svc_min_bl0_sec_ver_res_init(rom_error_t status,
                                       boot_svc_min_bl0_sec_ver_res_t *msg) {
  msg->status = status;
  boot_svc_header_finalize(kBootSvcMinBl0SecVerResType,
                           sizeof(boot_svc_min_bl0_sec_ver_res_t),
                           &msg->header);
}
