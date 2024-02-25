// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
#ifndef OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_DRIVERS_SPI_HOST_H_
#define OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_DRIVERS_SPI_HOST_H_

#include <stdalign.h>
#include <stddef.h>
#include <stdint.h>

#include "sw/lib/sw/device/silicon_creator/error.h"

#ifdef __cplusplus
extern "C" {
#endif

/**
 * Width of SPI operations.
 */
typedef enum spi_host_width {
  /** Standard SPI mode (single lanes for send and recv). */
  kSpiHostWidthStandard = 0,
  /** Dual SPI mode (use two lanes for send and recv). */
  kSpiHostWidthDual = 1,
  /** Quad SPI mode (use four lanes for send and recv). */
  kSpiHostWidthQuad = 2,
} spi_host_width_t;

/**
 * Direction of SPI operations.
 *
 * This describes which direction a given SPI operation will use.
 */
typedef enum spi_host_direction {
  /** The SPI host neither transmits or receives. */
  kSpiHostDirectionDummy = 0,
  /** The SPI host receives data. */
  kSpiHostDirectionRx = 1,
  /** The SPI host transmits data. */
  kSpiHostDirectionTx = 2,
} spi_host_direction_t;

/**
 * Segment types for segments in a transaction.
 */
typedef enum spi_host_segment_type {
  /** The segment is a SPI opcode. */
  kSpiHostSegmentTypeOpcode,
  /** The segment is a SPI address. */
  kSpiHostSegmentTypeAddress,
  /** The segment is a SPI dummy cycle. */
  kSpiHostSegmentTypeDummy,
  /** The segment is a SPI transmit (from a memory buffer). */
  kSpiHostSegmentTypeTx,
  /** The segment is a SPI receive (into a memory buffer). */
  kSpiHostSegmentTypeRx,
} spi_host_segment_type_t;

/**
 * Address mode for the address segment in a transaction.
 */
typedef enum spi_host_addr_mode {
  /** The address is a 3-byte address. */
  kSpiHostAddrMode3b,
  /** The address is a 4-byte address. */
  kSpiHostAddrMode4b,
} spi_host_addr_mode_t;

/**
 * Segment descriptor for each segment in a transaction.
 *
 * This struct is a tagged union: the `type` field determines
 * which field of the union is relevant.
 */
typedef struct spi_host_segment {
  /** The segment type for this segment. */
  spi_host_segment_type_t type;
  spi_host_width_t width;
  union {
    struct {
      uint8_t opcode;
    } opcode;
    struct {
      spi_host_addr_mode_t mode;
      uint32_t address;
    } address;
    struct {
      size_t length;
    } dummy;
    struct {
      const void *buf;
      size_t length;
    } tx;
    struct {
      void *buf;
      size_t length;
    } rx;
  };
} spi_host_segment_t;

/**
 * Initializes the SPI host.
 *
 * @param precalculated_div DIVIDER value used to set the speed of the SPI_HOST.
 */
void spi_host_init(uint32_t precalculated_div);

/**
 * Perform a SPI transaction.
 *
 * @param csid The chip-select ID of the SPI target.
 * @param segments The SPI segments to send in this transaction.
 * @param length The number of SPI segments in this transaction.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
rom_error_t spi_host_transaction(uint32_t csid,
                                 const spi_host_segment_t *segments,
                                 size_t length);

#ifdef __cplusplus
}
#endif

#endif  // OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_DRIVERS_SPI_HOST_H_
