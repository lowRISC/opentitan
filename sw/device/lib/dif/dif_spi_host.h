// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_DIF_DIF_SPI_HOST_H_
#define OPENTITAN_SW_DEVICE_LIB_DIF_DIF_SPI_HOST_H_
/**
 * @file
 * @brief <a href="/hw/ip/spi_host/doc/">SPI Host</a> Device Interface Functions
 */

#include <stdint.h>

#include "sw/device/lib/dif/autogen/dif_spi_host_autogen.h"

#ifdef __cplusplus
extern "C" {
#endif  // __cplusplus

/**
 * Runtime configuration for SPI Host.
 *
 * This struct describes (SOFTWARE) runtime information for one-time
 * configuration of the hardware.
 */
typedef struct dif_spi_host_config {
  /** Desired SPI clock frequency (SCK). */
  uint32_t spi_clock;
  /** Peripheral clock frequency (ie: kClockFreqPeripheralHz). */
  uint32_t peripheral_clock_freq_hz;
  struct {
    /** Minimum idle time between commands in SCK half-cycles. */
    uint8_t idle;
    /** Chip-select trailing time in SCK half-cycles. */
    uint8_t trail;
    /** Chip-select leading time in SCK half-cycles. */
    uint8_t lead;
  } chip_select;
  /** Full-cycle sampling mode. */
  bool full_cycle;
  /** SPI clock phase. */
  bool cpha;
  /** SPI clock polarity. */
  bool cpol;
} dif_spi_host_config_t;

/**
 * Width of SPI operations.
 */
typedef enum dif_spi_host_width {
  /** Standard SPI mode (single lanes for send and recv). */
  kDifSpiHostWidthStandard = 0,
  /** Dual SPI mode (use two lanes for send and recv). */
  kDifSpiHostWidthDual = 1,
  /** Quad SPI mode (use four lanes for send and recv). */
  kDifSpiHostWidthQuad = 2,
} dif_spi_host_width_t;

/**
 * Direction of SPI operations.
 *
 * This describes which direction a given SPI operation will use.
 */
typedef enum dif_spi_host_direction {
  /** The SPI host neither transmits or receives. */
  kDifSpiHostDirectionDummy = 0,
  /** The SPI host receives data. */
  kDifSpiHostDirectionRx = 1,
  /** The SPI host transmits data. */
  kDifSpiHostDirectionTx = 2,
  /** The SPI host transmits and receives data. */
  kDifSpiHostDirectionBidirectional = 3,
} dif_spi_host_direction_t;

/**
 * Segment types for segments in a transaction.
 */
typedef enum dif_spi_host_segment_type {
  /** The segment is a SPI opcode. */
  kDifSpiHostSegmentTypeOpcode,
  /** The segment is a SPI address. */
  kDifSpiHostSegmentTypeAddress,
  /** The segment is a SPI dummy cycle. */
  kDifSpiHostSegmentTypeDummy,
  /** The segment is a SPI transmit (from a memory buffer). */
  kDifSpiHostSegmentTypeTx,
  /** The segment is a SPI receive (into a memory buffer). */
  kDifSpiHostSegmentTypeRx,
  /** The segment is a simultaneous transmit and receieve. */
  kDifSpiHostSegmentTypeBidirectional,
} dif_spi_host_segment_type_t;

/**
 * Address mode for the address segment in a transaction.
 */
typedef enum dif_spi_host_addr_mode {
  /** The address is a 3-byte address. */
  kDifSpiHostAddrMode3b,
  /** The address is a 4-byte address. */
  kDifSpiHostAddrMode4b,
} dif_spi_host_addr_mode_t;

/**
 * Segment descriptor for each segment in a transaction.
 *
 * This struct is a tagged union: the `type` field determines
 * which field of the union is relevant.
 */
typedef struct dif_spi_host_segment {
  /** The segment type for this segment. */
  dif_spi_host_segment_type_t type;
  union {
    uint8_t opcode;
    struct {
      dif_spi_host_width_t width;
      dif_spi_host_addr_mode_t mode;
      uint32_t address;
    } address;
    struct {
      dif_spi_host_width_t width;
      size_t length;
    } dummy;
    struct {
      dif_spi_host_width_t width;
      const void *buf;
      size_t length;
    } tx;
    struct {
      dif_spi_host_width_t width;
      void *buf;
      size_t length;
    } rx;
    struct {
      dif_spi_host_width_t width;
      const void *txbuf;
      void *rxbuf;
      size_t length;
    } bidir;
  };
} dif_spi_host_segment_t;

/**
 * Creates a new handle for SPI Host.
 *
 * This function does not actuate the hardware.
 *
 * @param base_addr The MMIO base address of the IP.
 * @param params Hardware instantiation parameters. (optional, may remove)
 * @param[out] spi_host Out param for the initialized handle.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_spi_host_init(mmio_region_t base_addr,
                               dif_spi_host_t *spi_host);

/**
 * Configures SPI Host with runtime information.
 *
 * This function should only need to be called once for the lifetime of
 * `handle`.
 *
 * @param spi_host A SPI Host handle.
 * @param config Runtime configuration parameters.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_spi_host_configure(const dif_spi_host_t *spi_host,
                                    dif_spi_host_config_t config);

/**
 * Sets the enablement of the SPI host output buffers.
 *
 * @param spi_host A SPI Host handle.
 * @param enabled Enable or disable the output buffers.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_spi_host_output_set_enabled(const dif_spi_host_t *spi_host,
                                             bool enabled);

/**
 * Write to the SPI Host transmit FIFO.
 *
 * @param spi_host A SPI Host handle.
 * @param src A pointer to the buffer to transmit.
 * @param len The length of the transmit buffer.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_spi_host_fifo_write(const dif_spi_host_t *spi_host,
                                     const void *src, uint16_t len);

/**
 * Read from the SPI Host receive FIFO.
 *
 * @param spi_host A SPI Host handle.
 * @param dst A pointer to the buffer to receive the data.
 * @param len The length of the receive buffer.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_spi_host_fifo_read(const dif_spi_host_t *spi_host, void *dst,
                                    uint16_t len);

/**
 * Begins a SPI Host transaction.
 *
 * @param spi_host A SPI Host handle.
 * @param csid The chip-select ID of the SPI target.
 * @param segments The SPI segments to send in this transaction.
 * @param length The number of SPI segments in this transaction.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_spi_host_transaction(const dif_spi_host_t *spi_host,
                                      uint32_t csid,
                                      dif_spi_host_segment_t *segments,
                                      size_t length);

#ifdef __cplusplus
}  // extern "C"
#endif  // __cplusplus

#endif  // OPENTITAN_SW_DEVICE_LIB_DIF_DIF_SPI_HOST_H_
