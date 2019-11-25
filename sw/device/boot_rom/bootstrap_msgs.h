// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef _F_BOOTSTRAP_MSGS_H__
#define _F_BOOTSTRAP_MSGS_H__

#include "sw/device/lib/base/types.h"

#define RAW_BUFFER_SIZE 1024
#define FRAME_EOF_MARKER 0x80000000
#define FRAME_NO(k) ((k)&0xffffff)

typedef struct {
  /* SHA2 of the entire frame_t message starting at the |frame_num| offset. */
  uint32 hash[8];

  /* Frame number starting at 0. The last frame should be ord with
   * FRAME_EOF_MARKER. */
  uint32 frame_num;

  /* 0-based flash offset where the frame should be written to. */
  uint32 flash_offset;
} frame_hdr_t;

typedef struct {
  /* Frame header. See frame_hdr_t for details. */
  frame_hdr_t hdr;

  /* Frame data uint32 aligned. */
  uint32 data[(RAW_BUFFER_SIZE - sizeof(frame_hdr_t)) / sizeof(uint32)];
} frame_t;

/* Bootstrap error codes */
#define E_BS_ERASE 10
#define E_BS_NOTEMPTY 11
#define E_BS_WRITE 12

#endif  // _F_BOOTSTRAP_MSGS_H__
