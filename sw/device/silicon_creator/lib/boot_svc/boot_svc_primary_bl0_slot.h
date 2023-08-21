// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_BOOT_SVC_BOOT_SVC_PRIMARY_BL0_SLOT_H_
#define OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_BOOT_SVC_BOOT_SVC_PRIMARY_BL0_SLOT_H_

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
 *     -s 3799858683 --language=c
 *
 * Minimum Hamming distance: 17
 * Maximum Hamming distance: 17
 * Minimum Hamming weight: 14
 * Maximum Hamming weight: 17
 */
enum {
  kBootSvcPrimaryBl0SlotReqType = 0x3d6c47b8,
  kBootSvcPrimaryBl0SlotResType = 0xf2a4a609,
};

/**
 * A Set Primary Boot Slot request message.
 */
typedef struct boot_svc_primary_bl0_slot_req {
  /**
   * Boot services message header.
   */
  boot_svc_header_t header;
  /**
   * BL0 slot to set as primary.
   */
  uint32_t primary_bl0_slot;
} boot_svc_primary_bl0_slot_req_t;

OT_ASSERT_MEMBER_OFFSET(boot_svc_primary_bl0_slot_req_t, header, 0);
OT_ASSERT_MEMBER_OFFSET(boot_svc_primary_bl0_slot_req_t, primary_bl0_slot,
                        CHIP_BOOT_SVC_MSG_HEADER_SIZE);
OT_ASSERT_SIZE(boot_svc_primary_bl0_slot_req_t, 48);

/**
 * A Set Primary Boot Slot response message.
 */
typedef struct boot_svc_primary_bl0_slot_res {
  /**
   * Boot services message header.
   */
  boot_svc_header_t header;
  /**
   * Primary BL0 slot set by the boot service.
   */
  uint32_t primary_bl0_slot;
  /**
   * Status response from ROM_EXT.
   */
  rom_error_t status;
} boot_svc_primary_bl0_slot_res_t;

OT_ASSERT_MEMBER_OFFSET(boot_svc_primary_bl0_slot_res_t, header, 0);
OT_ASSERT_MEMBER_OFFSET(boot_svc_primary_bl0_slot_res_t, primary_bl0_slot,
                        CHIP_BOOT_SVC_MSG_HEADER_SIZE);
OT_ASSERT_MEMBER_OFFSET(boot_svc_primary_bl0_slot_res_t, status,
                        CHIP_BOOT_SVC_MSG_HEADER_SIZE + 4);
OT_ASSERT_SIZE(boot_svc_primary_bl0_slot_res_t, 52);

/**
 * Initialize an empty set primary bl0 slot request message.
 *
 * @param primary_bl0_slot The primary BL0 boot slot.
 * @param[out] msg Output buffer for the message.
 */
void boot_svc_primary_bl0_slot_req_init(uint32_t primary_bl0_slot,
                                        boot_svc_primary_bl0_slot_req_t *msg);

/**
 * Initialize an empty set primary bl0 slot response message.
 *
 * @param primary_bl0_slot The primary BL0 boot slot.
 * @param status Error status from processing the request.
 * @param[out] msg Output buffer for the message.
 */
void boot_svc_primary_bl0_slot_res_init(uint32_t primary_bl0_slot,
                                        rom_error_t status,
                                        boot_svc_primary_bl0_slot_res_t *msg);

#ifdef __cplusplus
}  // extern "C"
#endif  // __cplusplus

#endif  // OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_BOOT_SVC_BOOT_SVC_PRIMARY_BL0_SLOT_H_
