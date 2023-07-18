// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_BOOT_SVC_BOOT_SVC_NEXT_BOOT_BL0_SLOT_H_
#define OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_BOOT_SVC_BOOT_SVC_NEXT_BOOT_BL0_SLOT_H_

#include <stdint.h>

#include "sw/device/lib/base/macros.h"
#include "sw/device/silicon_creator/lib/base/chip.h"
#include "sw/device/silicon_creator/lib/boot_svc/boot_svc_header.h"
#include "sw/device/silicon_creator/lib/error.h"

#ifdef __cplusplus
extern "C" {
#endif  // __cplusplus

enum {
  /*
   * Encoding generated with
   * $ ./util/design/sparse-fsm-encode.py -d 6 -m 2 -n 32 \
   *     -s 2121036560 --language=c
   *
   * Minimum Hamming distance: 14
   * Maximum Hamming distance: 14
   * Minimum Hamming weight: 11
   * Maximum Hamming weight: 13
   */
  kBootSvcNextBootBl0SlotA = 0x08c0d499,
  kBootSvcNextBootBl0SlotB = 0x7821e03a,

  /*
   *  Encoding generated with
   *  $ ./util/design/sparse-fsm-encode.py -d 6 -m 2 -n 32 \
   *      -s 3290097361 --language=c
   *
   * Minimum Hamming distance: 15
   * Maximum Hamming distance: 15
   * Minimum Hamming weight: 16
   * Maximum Hamming weight: 19
   */
  kBootSvcNextBl0SlotReqType = 0xe1edf546,
  kBootSvcNextBl0SlotResType = 0x657051be,
};

/**
 * A Next Boot BL0 Slot request message.
 */
typedef struct boot_svc_next_boot_bl0_slot_req {
  /**
   * Boot services message header.
   */
  boot_svc_header_t header;
  /**
   * BL0 slot to boot on next reboot.
   */
  uint32_t next_bl0_slot;
} boot_svc_next_boot_bl0_slot_req_t;

OT_ASSERT_MEMBER_OFFSET(boot_svc_next_boot_bl0_slot_req_t, header, 0);
OT_ASSERT_MEMBER_OFFSET(boot_svc_next_boot_bl0_slot_req_t, next_bl0_slot,
                        CHIP_BOOT_SVC_MSG_HEADER_SIZE);
OT_ASSERT_SIZE(boot_svc_next_boot_bl0_slot_req_t, 48);

/**
 * A Next Boot BL0 Slot response message.
 */
typedef struct boot_svc_next_boot_bl0_slot_res {
  /**
   * Boot services message header.
   */
  boot_svc_header_t header;
  /**
   * Response status from the ROM_EXT.
   */
  rom_error_t status;
} boot_svc_next_boot_bl0_slot_res_t;

OT_ASSERT_MEMBER_OFFSET(boot_svc_next_boot_bl0_slot_res_t, header, 0);
OT_ASSERT_MEMBER_OFFSET(boot_svc_next_boot_bl0_slot_res_t, status,
                        CHIP_BOOT_SVC_MSG_HEADER_SIZE);
OT_ASSERT_SIZE(boot_svc_next_boot_bl0_slot_res_t, 48);

/**
 * Initialize a Next Boot BL0 Slot Request message.
 *
 * @param next_slot Slot to boot into on reboot.
 * @param[out] msg Output buffer for the message.
 */
void boot_svc_next_boot_bl0_slot_req_init(
    uint32_t next_slot, boot_svc_next_boot_bl0_slot_req_t *msg);

/**
 * Initialize a Next Boot BL0 Slot Response message.
 *
 * @param status Reponse from the ROM_EXT after receiving the request.
 * @param[out] msg Output buffer for the message.
 */
void boot_svc_next_boot_bl0_slot_res_init(
    rom_error_t status, boot_svc_next_boot_bl0_slot_res_t *msg);

#ifdef __cplusplus
}  // extern "C"
#endif  // __cplusplus

#endif  // OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_BOOT_SVC_BOOT_SVC_NEXT_BOOT_BL0_SLOT_H_
