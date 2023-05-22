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
  /** If `EVENT_ENABLE.TXWM` is set, an interrupt will fire when the depth of
   * the TX FIFO drops below `TX_WATERMARK` words (32b each). */
  size_t tx_watermark;
  /** If `EVENT_ENABLE.RXWM` is set, an interrupt will fire when the depth of
   * the RX FIFO drops below `RX_WATERMARK` words (32b each). */
  size_t rx_watermark;
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

typedef enum dif_spi_host_events {
  /**
   * Enable IRQ to be fired when `STATUS.RXFULL` goes high.
   */
  kDifSpiHostEvtRxFull = 1 << 0,
  /**
   * Enable IRQ to be fired when `STATUS.TXEMPTY` goes high.
   */
  kDifSpiHostEvtTxEmpty = 1 << 1,
  /**
   * Enable IRQ to be fired when the number of 32-bit words in the RX FIFO is
   * greater than `CONTROL.RX_WATERMARK`.
   */
  kDifSpiHostEvtRxWm = 1 << 2,
  /**
   * Enable IRQ to be fired when the number of 32-bit words in the TX FIFO is
   * greater than `CONTROL.TX_WATERMARK`.
   */
  kDifSpiHostEvtTxWm = 1 << 3,
  /**
   * Enable IRQ to be fired when `STATUS.READY` goes high.
   */
  kDifSpiHostEvtReady = 1 << 4,
  /**
   * Enable IRQ to be fired when `STATUS.ACTIVE` goes low.
   */
  kDifSpiHostEvtIdle = 1 << 5,
  /**
   * All above together.
   */
  kDifSpiHostEvtAll = (1 << 6) - 1,
} dif_spi_host_events_code_t;

/**
 * Bitmask with the `dif_spi_host_events_code_t` values.
 */
typedef uint32_t dif_spi_host_events_t;

/**
 * Set the enable state of the spi host events.
 *
 * @param spi_host A SPI Host handle.
 * @param events A bitmask with the events to be enabled or disabled.
 * @param enable True to enable the `events` or false to disable.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_spi_host_event_set_enabled(const dif_spi_host_t *spi_host,
                                            dif_spi_host_events_t events,
                                            bool enable);

/**
 * Get the enabled events.
 *
 * @param spi_host A SPI Host handle.
 * @param[out] events A bitmask that will contain all the events that are
 * enabled.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_spi_host_event_get_enabled(const dif_spi_host_t *spi_host,
                                            dif_spi_host_events_t *events);

typedef struct dif_spi_host_status {
  /**
   * Indicates the SPI host is ready to receive commands.
   */
  bool ready;
  /**
   * Indicates the SPI host is processing a previously issued command.
   */
  bool active;
  /**
   * Indicates that the transmit data fifo is full.
   */
  bool tx_full;
  /**
   * Indicates that the transmit data fifo is empty.
   */
  bool tx_empty;
  /**
   * If true, signifies that an ongoing transaction has stalled due to lack of
   * data in the`TX FIFO`.
   */
  bool tx_stall;
  /**
   * If true, the amount of data in the `TX FIFO` has fallen below the
   * level of `CONTROL.TX_WATERMARK`words (32b each).
   */
  bool tx_water_mark;
  /**
   * Indicates that the receive fifo is full. Any ongoing transactions will
   * stall until firmware reads some data from `RXDATA`.
   */
  bool rx_full;
  /**
   * Indicates that the receive fifo is empty. Any reads from `RX FIFO` will
   * cause an error interrupt.
   */
  bool rx_empty;
  /**
   * If true, signifies that an ongoing transaction has stalled due to lack of
   * available space in the `RX FIFO`.
   */
  bool rx_stall;
  /**
   * If true the least significant bits will be transmitted first.
   */
  bool least_significant_first;
  /**
   * If true, the number of 32-bits in the `RX FIFO` now exceeds the
   * `CONTROL.RX_WATERMARK`entries (32b each).
   */
  bool rx_water_mark;
  /**
   * Indicates how many unread 32-bit words are currently in the command
   * segment queue.
   */
  uint32_t cmd_queue_depth;
  /**
   * Indicates how many unread 32-bit words are currently in the `RX FIFO`.
   * When active, this result may an underestimate due to synchronization
   * delays.
   */
  uint32_t rx_queue_depth;
  /**
   * Indicates how many unsent 32-bit words are currently in the`TX FIFO`.
   */
  uint32_t tx_queue_depth;
} dif_spi_host_status_t;

/**
 * Read the current status of the spi host.
 *
 * @param spi_host A SPI Host handle.
 * @param[out] status The status of the spi.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_spi_host_get_status(const dif_spi_host_t *spi_host,
                                     dif_spi_host_status_t *status);

/**
 * Issues a command segment to a spi_host.
 *
 * @param spi_host A SPI Host handle.
 * @param length The number of 1-byte burst for read and write segments, or the
 * number of cycles for dummy segments.
 * @param speed Which speed the transmission should use.
 * @param direction Which direction the operation should use.
 * @param last_segment If true the chip select line is raised after the
 * transmission, otherwise it is kept low.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_spi_host_write_command(const dif_spi_host_t *spi_host,
                                        uint16_t length,
                                        dif_spi_host_width_t speed,
                                        dif_spi_host_direction_t direction,
                                        bool last_segment);

typedef enum dif_spi_host_error_code {
  /**
   * Indicates a write to `COMMAND` when `STATUS.READY = 0`.
   */
  kDifSpiHostErrorCmdBusy = 1 << 0,
  /**
   * Indicates that firmware has overflowed the `TX FIFO`.
   */
  kDifSpiHostErrorOverflow = 1 << 1,
  /**
   * Indicates that firmware has attempted to read from `RXDATA` when the `RX
   * FIFO` is empty.
   */
  kDifSpiHostErrorUnderflow = 1 << 2,
  /**
   * Indicates an invalid command segment, meaning either an invalid value of
   * `COMMAND.SPEED` or a request for bidirectional data transfer at dual or
   * quad speed.
   */
  kDifSpiHostErrorCmdInval = 1 << 3,
  /**
   * Indicates a command was attempted with an invalid value for `CSID`.
   */
  kDifSpiHostErrorCsIdIval = 1 << 4,
  /**
   * Indicates that TL-UL attempted to write to `TXDATA` with no bytes enabled.
   * Such ‘zero byte’ writes are not supported. Note: This error does not
   * generate IRQ.
   */
  kDifSpiHostErrorAccessIval = 1 << 5,
  /**
   * All the errors that can generate an IRQ.
   */
  kDifSpiHostIrqErrorAll = (1 << 5) - 1,
  /**
   * All the errors above together.
   */
  kDifSpiHostErrorAll = (1 << 6) - 1,
} dif_spi_host_error_code_t;

/**
 * Bitmask with the `dif_spi_host_error_code_t` values.
 */
typedef uint32_t dif_spi_host_errors_t;

/**
 * Set the enable state of the spi host errors.
 *
 * @param spi_host A SPI Host handle.
 * @param errors A bitmask with the errors to be enabled or disabled.
 * @param enable True to enable the `events` or false to disable.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_spi_host_error_set_enabled(const dif_spi_host_t *spi_host,
                                            dif_spi_host_errors_t errors,
                                            bool enable);

/**
 * Get the enabled errors.
 *
 * @param spi_host A SPI Host handle.
 * @param[out] errors A bitmask that will contain all the errors that are
 * enabled.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_spi_host_error_get_enabled(const dif_spi_host_t *spi_host,
                                            dif_spi_host_errors_t *errors);

/**
 * Read the current error status of the spi host.
 *
 * @param spi_host A SPI Host handle.
 * @param[out] errors The error status of the spi.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_spi_host_get_error(const dif_spi_host_t *spi_host,
                                    dif_spi_host_errors_t *errors);
#ifdef __cplusplus
}  // extern "C"
#endif  // __cplusplus

#endif  // OPENTITAN_SW_DEVICE_LIB_DIF_DIF_SPI_HOST_H_
