// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_BOOT_SVC_BOOT_SVC_MIN_BL0_SEC_VER_H_
#define OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_BOOT_SVC_BOOT_SVC_MIN_BL0_SEC_VER_H_

#include <stdint.h>

#include "sw/device/lib/base/macros.h"
#include "sw/device/silicon_creator/lib/boot_svc/boot_svc_header.h"
#include "sw/device/silicon_creator/lib/error.h"

#ifdef __cplusplus
extern "C" {
#endif  // __cplusplus

/*
 * Encoding generated with
 * $ ./util/design/sparse-fsm-encode.py -d 6 -m 2 -n 32 \
 *     -s 1625797253 --language=c
 *
 * Minimum Hamming distance: 20
 * Maximum Hamming distance: 20
 * Minimum Hamming weight: 17
 * Maximum Hamming weight: 19
 */
enum {
  kBootSvcMinBl0SecVerReqType = 0xdac59e6e,
  kBootSvcMinBl0SecVerResType = 0x756385f1,
};

/**
 * A Set Minimum Security Version request.
 */
typedef struct boot_svc_min_bl0_sec_ver_req {
  /**
   * Boot services message header.
   */
  boot_svc_header_t header;
  /**
   * Minimum security version to set.
   */
  uint32_t min_bl0_sec_ver;
} boot_svc_min_bl0_sec_ver_req_t;

OT_ASSERT_MEMBER_OFFSET(boot_svc_min_bl0_sec_ver_req_t, header, 0);
OT_ASSERT_MEMBER_OFFSET(boot_svc_min_bl0_sec_ver_req_t, min_bl0_sec_ver,
                        CHIP_BOOT_SVC_MSG_HEADER_SIZE);
OT_ASSERT_SIZE(boot_svc_min_bl0_sec_ver_req_t, 48);

/**
 * A Set Minimum Security Version response.
 */
typedef struct boot_svc_min_bl0_sec_ver_res {
  /**
   * Boot services message header.
   */
  boot_svc_header_t header;
  /**
   * Minimum security version to set.
   */
  rom_error_t status;
} boot_svc_min_bl0_sec_ver_res_t;

OT_ASSERT_MEMBER_OFFSET(boot_svc_min_bl0_sec_ver_res_t, header, 0);
OT_ASSERT_MEMBER_OFFSET(boot_svc_min_bl0_sec_ver_res_t, status,
                        CHIP_BOOT_SVC_MSG_HEADER_SIZE);
OT_ASSERT_SIZE(boot_svc_min_bl0_sec_ver_res_t, 48);

/**
 * Initialize a set minimum security version request message.
 *
 * @param min_bl0_sec_ver_version The minimum security version to set.
 * @param[out] msg Output buffer for the message.
 */
void boot_svc_min_bl0_sec_ver_req_init(uint32_t min_bl0_sec_ver_version,
                                       boot_svc_min_bl0_sec_ver_req_t *msg);

/**
 * Initialize a set minimum security version response message.
 *
 * @param status The result of this request.
 * @param[out] msg Output buffer for the message.
 */
void boot_svc_min_bl0_sec_ver_res_init(rom_error_t status,
                                       boot_svc_min_bl0_sec_ver_res_t *msg);

#ifdef __cplusplus
}  // extern "C"
#endif  // __cplusplus

#endif  // OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_BOOT_SVC_BOOT_SVC_MIN_BL0_SEC_VER_H_
