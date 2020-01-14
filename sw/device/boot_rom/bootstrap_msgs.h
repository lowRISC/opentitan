// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_BOOT_ROM_BOOTSTRAP_MSGS_H_
#define OPENTITAN_SW_DEVICE_BOOT_ROM_BOOTSTRAP_MSGS_H_
#include <stdint.h>

#define RAW_BUFFER_SIZE 1024
#define FRAME_EOF_MARKER 0x80000000
#define FRAME_NO(k) ((k)&0xffffff)

typedef struct {
  /* SHA2 of the entire frame_t message starting at the |frame_num| offset. */
  uint32_t hash[8];

  /* Frame number starting at 0. The last frame should be ord with
   * FRAME_EOF_MARKER. */
  uint32_t frame_num;

  /* 0-based flash offset where the frame should be written to. */
  uint32_t flash_offset;
} frame_hdr_t;

typedef struct {
  /* Frame header. See frame_hdr_t for details. */
  frame_hdr_t hdr;

  /* Frame data uint32_t aligned. */
  uint32_t data[(RAW_BUFFER_SIZE - sizeof(frame_hdr_t)) / sizeof(uint32_t)];
} frame_t;

/* Bootstrap error codes */
#define E_BS_ERASE 10
#define E_BS_NOTEMPTY 11
#define E_BS_WRITE 12

#endif  // OPENTITAN_SW_DEVICE_BOOT_ROM_BOOTSTRAP_MSGS_H_
