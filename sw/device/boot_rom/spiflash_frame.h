// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_BOOT_ROM_SPIFLASH_FRAME_H_
#define OPENTITAN_SW_DEVICE_BOOT_ROM_SPIFLASH_FRAME_H_

#include <stdalign.h>
#include <stdint.h>

#include "sw/device/lib/hw_sha256.h"

/**
 * The total size of a spiflash frame.
 */
#define SPIFLASH_RAW_BUFFER_SIZE 2048

/**
 * The EOF flag on a spiflash frame, indicating that a frame is the last one in
 * the sequence.
 */
#define SPIFLASH_FRAME_EOF_MARKER 0x80000000

/**
 * Extracts the "number" part of a `frame_num`.
 */
#define SPIFLASH_FRAME_NUM(k) ((k)&0xffffff)

/**
 * Checks whether a `frame_num` represents an EOF.
 */
#define SPIFLASH_FRAME_IS_EOF(k) (((k)&SPIFLASH_FRAME_EOF_MARKER) != 0)

/**
 * The length, in words, of a frame's data buffer.
 */
#define SPIFLASH_FRAME_DATA_WORDS                                 \
  ((SPIFLASH_RAW_BUFFER_SIZE - sizeof(spiflash_frame_header_t)) / \
   sizeof(uint32_t))

/**
 * A spiflash frame header.
 */
typedef struct spiflash_frame_header {
  /**
   * SHA256 of the entire frame_t message starting at the `frame_num` offset.
   */
  uint32_t hash[SHA256_DIGEST_SIZE / sizeof(uint32_t)];
  /**
   * Frame number starting at 0. The last frame should be OR'd with
   * FRAME_EOF_MARKER.
   */
  uint32_t frame_num;
  /**
   * Offset in flash, indexed from 0, where the frame should be
   * written.
   */
  uint32_t flash_offset;
} spiflash_frame_header_t;

/**
 * A spiflash frame, as it would arrive on the wire.
 */
typedef struct spiflash_frame {
  /**
   * Frame header.
   */
  spiflash_frame_header_t header;
  /**
   * Frame data, word-aligned.
   */
  uint32_t data[SPIFLASH_FRAME_DATA_WORDS];
} spiflash_frame_t;

_Static_assert(sizeof(spiflash_frame_t) == SPIFLASH_RAW_BUFFER_SIZE,
               "spiflash_frame_t is the wrong size!");

#endif  // OPENTITAN_SW_DEVICE_BOOT_ROM_SPIFLASH_FRAME_H_
