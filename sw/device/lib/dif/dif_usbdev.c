// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/dif/dif_usbdev.h"

#include "sw/device/lib/base/bitfield.h"

#include "usbdev_regs.h"  // Generated.

/**
 * Definition in the header file (and probably other places) must be updated if
 * there is a hardware change.
 */
_Static_assert(USBDEV_NUM_ENDPOINTS == USBDEV_PARAM_NENDPOINTS,
               "Mismatch in number of endpoints");

/**
 * Max packet size is equal to the size of buffer entries.
 */
#define USBDEV_BUFFER_ENTRY_SIZE_BYTES USBDEV_MAX_PACKET_SIZE

/**
 * Bit index for the state of read buffer operation in
 * dif_usbdev_t.active_buffer_ops`. See the definition of `buffer_op_init`.
 */
#define USBDEV_READ_BUFFER_OP_BIT_INDEX 15

/**
 * Constants used to indicate that a buffer pool is full or empty.
 */
#define BUFFER_POOL_FULL (USBDEV_NUM_BUFFERS - 1)
#define BUFFER_POOL_EMPTY -1

/**
 * Hardware information for endpoints.
 */
typedef struct endpoint_hw_info {
  uint32_t config_in_reg_offset;
  uint8_t bit_index;
} endpoint_hw_info_t;

/**
 * Helper macro to define an `endpoint_hw_info_t` entry for endpoint N.
 *
 * Note: This uses the bit indices of `USBDEV_IN_SENT` register for the sake
 * of conciseness because other endpoint registers use the same layout.
 */
#define ENDPOINT_HW_INFO_ENTRY(N)                                  \
  [N] = {.config_in_reg_offset = USBDEV_CONFIGIN_##N##_REG_OFFSET, \
         .bit_index = USBDEV_IN_SENT_SENT_##N}

static const endpoint_hw_info_t kEndpointHwInfos[USBDEV_NUM_ENDPOINTS] = {
    ENDPOINT_HW_INFO_ENTRY(0),  ENDPOINT_HW_INFO_ENTRY(1),
    ENDPOINT_HW_INFO_ENTRY(2),  ENDPOINT_HW_INFO_ENTRY(3),
    ENDPOINT_HW_INFO_ENTRY(4),  ENDPOINT_HW_INFO_ENTRY(5),
    ENDPOINT_HW_INFO_ENTRY(6),  ENDPOINT_HW_INFO_ENTRY(7),
    ENDPOINT_HW_INFO_ENTRY(8),  ENDPOINT_HW_INFO_ENTRY(9),
    ENDPOINT_HW_INFO_ENTRY(10), ENDPOINT_HW_INFO_ENTRY(11),
};

#undef ENDPOINT_HW_INFO_ENTRY

/**
 * Mapping from `dif_usbdev_irq_t` to bit indices in interrupt registers.
 */
static const uint8_t kIrqEnumToBitIndex[] = {
        [kDifUsbdevIrqPktReceived] = USBDEV_INTR_COMMON_PKT_RECEIVED,
        [kDifUsbdevIrqPktSent] = USBDEV_INTR_COMMON_PKT_SENT,
        [kDifUsbdevIrqDisconnected] = USBDEV_INTR_COMMON_DISCONNECTED,
        [kDifUsbdevIrqHostLost] = USBDEV_INTR_COMMON_HOST_LOST,
        [kDifUsbdevIrqLinkReset] = USBDEV_INTR_COMMON_LINK_RESET,
        [kDifUsbdevIrqLinkSuspend] = USBDEV_INTR_COMMON_LINK_SUSPEND,
        [kDifUsbdevIrqLinkResume] = USBDEV_INTR_COMMON_LINK_RESUME,
        [kDifUsbdevIrqAvEmpty] = USBDEV_INTR_COMMON_AV_EMPTY,
        [kDifUsbdevIrqRxFull] = USBDEV_INTR_COMMON_RX_FULL,
        [kDifUsbdevIrqAvOverflow] = USBDEV_INTR_COMMON_AV_OVERFLOW,
        [kDifUsbdevIrqLinkInError] = USBDEV_INTR_COMMON_LINK_IN_ERR,
        [kDifUsbdevIrqRxCrcError] = USBDEV_INTR_COMMON_RX_CRC_ERR,
        [kDifUsbdevIrqRxPidError] = USBDEV_INTR_COMMON_RX_PID_ERR,
        [kDifUsbdevIrqRxBitstuffError] = USBDEV_INTR_COMMON_RX_BITSTUFF_ERR,
        [kDifUsbdevIrqFrame] = USBDEV_INTR_COMMON_FRAME,
        [kDifUsbdevIrqConnected] = USBDEV_INTR_COMMON_CONNECTED,
};

/**
 * Static functions for the free buffer pool.
 */

/**
 * Checks if a buffer pool is full.
 *
 * A buffer pool is full if it contains `USBDEV_NUM_BUFFERS` entries.
 *
 * @param pool A buffer pool.
 * @return `true` if the buffer pool if full, `false` otherwise.
 */
DIF_WARN_UNUSED_RESULT
static bool buffer_pool_is_full(dif_usbdev_buffer_pool_t *pool) {
  return pool->top == BUFFER_POOL_FULL;
}

/**
 * Checks if a buffer pool is empty.
 *
 * @param pool A buffer pool.
 * @return `true` if the buffer pool is empty, `false` otherwise.
 */
DIF_WARN_UNUSED_RESULT
static bool buffer_pool_is_empty(dif_usbdev_buffer_pool_t *pool) {
  return pool->top == BUFFER_POOL_EMPTY;
}

/**
 * Checks if a buffer entry is valid.
 *
 * An entry is valid if it is less than `USBDEV_NUM_BUFFERS`.
 *
 * @param entry A buffer entry.
 * @return `true` if the entry is valid, `false` otherwise.
 */
DIF_WARN_UNUSED_RESULT
static bool buffer_pool_is_valid_entry(uint8_t entry) {
  return entry < USBDEV_NUM_BUFFERS;
}

/**
 * Adds a buffer entry to a buffer pool.
 *
 * @param pool A buffer pool.
 * @param entry A buffer entry.
 * @return `true` if the operation was successful, `false` otherwise.
 */
DIF_WARN_UNUSED_RESULT
static bool buffer_pool_add(dif_usbdev_buffer_pool_t *pool, uint8_t entry) {
  if (buffer_pool_is_full(pool) || !buffer_pool_is_valid_entry(entry)) {
    return false;
  }

  ++pool->top;
  pool->entries[pool->top] = entry;

  return true;
}

/**
 * Removes a buffer entry from a buffer pool.
 *
 * @param pool A buffer pool.
 * @param entry A buffer entry.
 * @return `true` if the operation was successful, `false` otherwise.
 */
DIF_WARN_UNUSED_RESULT
static bool buffer_pool_remove(dif_usbdev_buffer_pool_t *pool, uint8_t *entry) {
  if (buffer_pool_is_empty(pool) || entry == NULL) {
    return false;
  }

  *entry = pool->entries[pool->top];
  --pool->top;

  return true;
}

/**
 * Initializes the buffer pool.
 *
 * At the end of this operation, the buffer pool contains `USBDEV_NUM_BUFFERS`
 * buffer entries.
 *
 * @param pool A buffer pool.
 * @return `true` if the operation was successful, `false` otherwise.
 */
DIF_WARN_UNUSED_RESULT
static bool buffer_pool_init(dif_usbdev_buffer_pool_t *pool) {
  // Start with an empty pool
  pool->top = -1;

  // Add all entries
  for (uint8_t i = 0; i < USBDEV_NUM_BUFFERS; ++i) {
    if (!buffer_pool_add(pool, i)) {
      return false;
    }
  }

  return true;
}

/**
 * Static functions for managing read and write buffer operations.
 */

/**
 * Initializes the `active_buffer_ops` field of a `dif_usbdev_t`.
 *
 * In `dif_usbdev_t.active_buffer_ops`:
 * - Bits 0..11: True if writing bytes of an outgoing packet for endpoint N
 * (0..11).
 * - Bits 12..14: Unused.
 * - Bit 15: True if reading bytes of an incoming packet.
 */
static void buffer_op_init(dif_usbdev_t *usbdev) {
  usbdev->active_buffer_ops = 0;
}

/**
 * Mark the start of a buffer write operation for an endpoint.
 *
 * @param usbdev A USB device.
 * @param endpoint An endpoint.
 */
static void buffer_op_start_write(dif_usbdev_t *usbdev, uint8_t endpoint) {
  usbdev->active_buffer_ops = bitfield_field32_write(
      usbdev->active_buffer_ops,
      (bitfield_field32_t){
          .mask = 1, .index = kEndpointHwInfos[endpoint].bit_index,
      },
      1);
}

/**
 * Mark the end of a buffer write operation for an endpoint.
 *
 * @param usbdev A USB device.
 * @param endpoint An endpoint.
 */
static void buffer_op_stop_write(dif_usbdev_t *usbdev, uint8_t endpoint) {
  usbdev->active_buffer_ops = bitfield_field32_write(
      usbdev->active_buffer_ops,
      (bitfield_field32_t){
          .mask = 1, .index = kEndpointHwInfos[endpoint].bit_index,
      },
      0);
}

/**
 * Check if there is an active buffer write operation for an endpoint.
 *
 * @param usbdev A USB device.
 * @param endpoint An endpoint.
 * @return `true` if there is an active buffer write operation for the endpoint,
 * `false` otherwise.
 */
DIF_WARN_UNUSED_RESULT
static bool buffer_op_is_writing(dif_usbdev_t *usbdev, uint8_t endpoint) {
  return bitfield_field32_read(
             usbdev->active_buffer_ops,
             (bitfield_field32_t){
                 .mask = 1, .index = kEndpointHwInfos[endpoint].bit_index,
             }) > 0;
}

/**
 * Mark the start of a buffer read operation for an endpoint.
 *
 * @param usbdev A USB device.
 * @param endpoint An endpoint.
 */
static void buffer_op_start_read(dif_usbdev_t *usbdev) {
  usbdev->active_buffer_ops = bitfield_field32_write(
      usbdev->active_buffer_ops,
      (bitfield_field32_t){
          .mask = 1, .index = USBDEV_READ_BUFFER_OP_BIT_INDEX,
      },
      1);
}

/**
 * Mark the end of a buffer read operation for an endpoint.
 *
 * @param usbdev A USB device.
 * @param endpoint An endpoint.
 */
static void buffer_op_stop_read(dif_usbdev_t *usbdev) {
  usbdev->active_buffer_ops = bitfield_field32_write(
      usbdev->active_buffer_ops,
      (bitfield_field32_t){
          .mask = 1, .index = USBDEV_READ_BUFFER_OP_BIT_INDEX,
      },
      0);
}

/**
 * Check if there is an active buffer read operation for an endpoint.
 *
 * @param usbdev A USB device.
 * @param endpoint An endpoint.
 * @return `true` if there is an active buffer read operation for the endpoint,
 * `false` otherwise.
 */
DIF_WARN_UNUSED_RESULT
static bool buffer_op_is_reading(dif_usbdev_t *usbdev) {
  return bitfield_field32_read(
             usbdev->active_buffer_ops,
             (bitfield_field32_t){
                 .mask = 1, .index = USBDEV_READ_BUFFER_OP_BIT_INDEX,
             }) > 0;
}

/**
 * Utility functions
 */

/**
 * Checks if the given value is a valid `dif_usbdev_toggle_t` variant.
 */
DIF_WARN_UNUSED_RESULT
static bool is_valid_toggle(dif_usbdev_toggle_t val) {
  return val == kDifUsbdevToggleEnable || val == kDifUsbdevToggleDisable;
}

/**
 * Checks if the given value is a valid `dif_usbdev_power_sense_override_t`
 * variant.
 */
DIF_WARN_UNUSED_RESULT
static bool is_valid_power_sense_override(
    dif_usbdev_power_sense_override_t val) {
  return val == kDifUsbdevPowerSenseOverrideDisabled ||
         val == kDifUsbdevPowerSenseOverridePresent ||
         val == kDifUsbdevPowerSenseOverrideNotPresent;
}

/**
 * Checks if the given value is a valid endpoint number.
 */
DIF_WARN_UNUSED_RESULT
static bool is_valid_endpoint(uint8_t endpoint) {
  return endpoint < USBDEV_NUM_ENDPOINTS;
}

/**
 * Checks if the given value is a valid `dif_usbdev_irq_t` variant.
 */
DIF_WARN_UNUSED_RESULT
static bool is_valid_irq(dif_usbdev_irq_t irq) {
  return irq >= kDifUsbdevIrqFirst && irq <= kDifUsbdevIrqLast;
}

/**
 * Enables/disables the functionality controlled by the register at `reg_offset`
 * for an endpoint.
 */
DIF_WARN_UNUSED_RESULT
static dif_usbdev_result_t endpoint_functionality_enable(
    dif_usbdev_t *usbdev, uint32_t reg_offset, uint8_t endpoint,
    dif_usbdev_toggle_t new_state) {
  if (usbdev == NULL || !is_valid_endpoint(endpoint) ||
      !is_valid_toggle(new_state)) {
    return kDifUsbdevBadArg;
  }

  if (kDifUsbdevToggleEnable) {
    mmio_region_nonatomic_set_bit32(usbdev->base_addr, reg_offset,
                                    kEndpointHwInfos[endpoint].bit_index);
  } else {
    mmio_region_nonatomic_clear_bit32(usbdev->base_addr, reg_offset,
                                      kEndpointHwInfos[endpoint].bit_index);
  }

  return kDifUsbdevOK;
}

/**
 * Returns the address that corresponds to the given buffer entry and offset
 * into that entry.
 */
DIF_WARN_UNUSED_RESULT
static uint32_t get_buffer_addr(uint8_t buffer_entry, size_t offset) {
  return USBDEV_BUFFER_REG_OFFSET +
         (buffer_entry * USBDEV_BUFFER_ENTRY_SIZE_BYTES) + offset;
}

/**
 * USBDEV DIF library functions.
 */

dif_usbdev_result_t dif_usbdev_init(dif_usbdev_config_t *config,
                                    dif_usbdev_t *usbdev) {
  if (usbdev == NULL || config == NULL) {
    return kDifUsbdevBadArg;
  }

  // Check enum fields
  if (!is_valid_toggle(config->differential_rx) ||
      !is_valid_toggle(config->differential_tx) ||
      !is_valid_toggle(config->single_bit_eop) ||
      !is_valid_power_sense_override(config->power_sense_override)) {
    return kDifUsbdevBadArg;
  }

  // Store base address
  usbdev->base_addr = config->base_addr;

  // Initialize the free buffer pool
  if (!buffer_pool_init(&usbdev->buffer_pool)) {
    return kDifUsbdevError;
  }

  // No active buffer operation
  buffer_op_init(usbdev);

  // Determine the value of the PHY_CONFIG register.
  uint32_t phy_config_val = 0;

  if (config->differential_rx == kDifUsbdevToggleEnable) {
    phy_config_val = bitfield_field32_write(
        phy_config_val,
        (bitfield_field32_t){
            .mask = 1, .index = USBDEV_PHY_CONFIG_RX_DIFFERENTIAL_MODE,
        },
        1);
  }

  if (config->differential_tx == kDifUsbdevToggleEnable) {
    phy_config_val = bitfield_field32_write(
        phy_config_val,
        (bitfield_field32_t){
            .mask = 1, .index = USBDEV_PHY_CONFIG_TX_DIFFERENTIAL_MODE,
        },
        1);
  }

  if (config->single_bit_eop == kDifUsbdevToggleEnable) {
    phy_config_val = bitfield_field32_write(
        phy_config_val,
        (bitfield_field32_t){
            .mask = 1, .index = USBDEV_PHY_CONFIG_EOP_SINGLE_BIT,
        },
        1);
  }

  if (config->power_sense_override == kDifUsbdevPowerSenseOverridePresent) {
    phy_config_val = bitfield_field32_write(
        phy_config_val,
        (bitfield_field32_t){
            .mask = 1, .index = USBDEV_PHY_CONFIG_OVERRIDE_PWR_SENSE_EN,
        },
        1);
    phy_config_val = bitfield_field32_write(
        phy_config_val,
        (bitfield_field32_t){
            .mask = 1, .index = USBDEV_PHY_CONFIG_OVERRIDE_PWR_SENSE_VAL,
        },
        1);
  } else if (config->power_sense_override ==
             kDifUsbdevPowerSenseOverrideNotPresent) {
    phy_config_val = bitfield_field32_write(
        phy_config_val,
        (bitfield_field32_t){
            .mask = 1, .index = USBDEV_PHY_CONFIG_OVERRIDE_PWR_SENSE_EN,
        },
        1);
  }

  // Write configuration to PHY_CONFIG register
  mmio_region_write32(usbdev->base_addr, USBDEV_PHY_CONFIG_REG_OFFSET,
                      phy_config_val);

  return kDifUsbdevOK;
}

dif_usbdev_result_t dif_usbdev_fill_available_fifo(dif_usbdev_t *usbdev) {
  if (usbdev == NULL) {
    return kDifUsbdevBadArg;
  }

  // Remove entries from the pool and write them to the AV FIFO until it is full
  while (!mmio_region_get_bit32(usbdev->base_addr, USBDEV_USBSTAT_REG_OFFSET,
                                USBDEV_USBSTAT_AV_FULL) &&
         !buffer_pool_is_empty(&usbdev->buffer_pool)) {
    uint8_t buffer_entry;
    if (!buffer_pool_remove(&usbdev->buffer_pool, &buffer_entry)) {
      return kDifUsbdevError;
    }
    mmio_region_write_only_set_field32(
        usbdev->base_addr, USBDEV_AVBUFFER_REG_OFFSET,
        (bitfield_field32_t){
            .mask = USBDEV_AVBUFFER_BUFFER_MASK,
            .index = USBDEV_AVBUFFER_BUFFER_OFFSET,
        },
        buffer_entry);
  }

  return kDifUsbdevOK;
}

dif_usbdev_result_t dif_usbdev_endpoint_setup_enable(
    dif_usbdev_t *usbdev, uint8_t endpoint, dif_usbdev_toggle_t new_state) {
  return endpoint_functionality_enable(usbdev, USBDEV_RXENABLE_SETUP_REG_OFFSET,
                                       endpoint, new_state);
}

dif_usbdev_result_t dif_usbdev_endpoint_out_enable(
    dif_usbdev_t *usbdev, uint8_t endpoint, dif_usbdev_toggle_t new_state) {
  return endpoint_functionality_enable(usbdev, USBDEV_RXENABLE_OUT_REG_OFFSET,
                                       endpoint, new_state);
}

dif_usbdev_result_t dif_usbdev_endpoint_stall_enable(
    dif_usbdev_t *usbdev, uint8_t endpoint, dif_usbdev_toggle_t new_state) {
  return endpoint_functionality_enable(usbdev, USBDEV_STALL_REG_OFFSET,
                                       endpoint, new_state);
}

dif_usbdev_result_t dif_usbdev_endpoint_stall_get(dif_usbdev_t *usbdev,
                                                  uint8_t endpoint,
                                                  bool *state) {
  if (usbdev == NULL || state == NULL || !is_valid_endpoint(endpoint)) {
    return kDifUsbdevBadArg;
  }

  *state = mmio_region_get_bit32(usbdev->base_addr, USBDEV_STALL_REG_OFFSET,
                                 kEndpointHwInfos[endpoint].bit_index);

  return kDifUsbdevOK;
}

dif_usbdev_result_t dif_usbdev_endpoint_iso_enable(
    dif_usbdev_t *usbdev, uint8_t endpoint, dif_usbdev_toggle_t new_state) {
  return endpoint_functionality_enable(usbdev, USBDEV_ISO_REG_OFFSET, endpoint,
                                       new_state);
}

dif_usbdev_result_t dif_usbdev_interface_enable(dif_usbdev_t *usbdev,
                                                dif_usbdev_toggle_t new_state) {
  if (usbdev == NULL || !is_valid_toggle(new_state)) {
    return kDifUsbdevBadArg;
  }

  if (new_state == kDifUsbdevToggleEnable) {
    mmio_region_nonatomic_set_bit32(
        usbdev->base_addr, USBDEV_USBCTRL_REG_OFFSET, USBDEV_USBCTRL_ENABLE);
  } else {
    mmio_region_nonatomic_clear_bit32(
        usbdev->base_addr, USBDEV_USBCTRL_REG_OFFSET, USBDEV_USBCTRL_ENABLE);
  }

  return kDifUsbdevOK;
}

dif_usbdev_rx_packet_get_info_result_t dif_usbdev_rx_packet_get_info(
    dif_usbdev_t *usbdev, dif_usbdev_rx_packet_info_t *packet) {
  if (usbdev == NULL || packet == NULL) {
    return kDifUsbdevRxPacketGetInfoResultBadArg;
  }

  // Check if there is already a read buffer operation in progress
  if (buffer_op_is_reading(usbdev)) {
    return kDifUsbdevRxPacketGetInfoResultBusy;
  }

  // Check if the RX FIFO is empty
  if (mmio_region_get_bit32(usbdev->base_addr, USBDEV_USBSTAT_REG_OFFSET,
                            USBDEV_USBSTAT_RX_EMPTY)) {
    return kDifUsbdevRxPacketGetInfoResultNoPackets;
  }

  // Read fifo entry
  const uint32_t fifo_entry =
      mmio_region_read32(usbdev->base_addr, USBDEV_RXFIFO_REG_OFFSET);
  // Fill packet info
  packet->endpoint = bitfield_field32_read(
      fifo_entry,
      (bitfield_field32_t){
          .mask = USBDEV_RXFIFO_EP_MASK, .index = USBDEV_RXFIFO_EP_OFFSET,
      });
  packet->is_setup = bitfield_field32_read(
      fifo_entry, (bitfield_field32_t){
                      .mask = 1, .index = USBDEV_RXFIFO_SETUP,
                  });
  packet->len = bitfield_field32_read(
      fifo_entry,
      (bitfield_field32_t){
          .mask = USBDEV_RXFIFO_SIZE_MASK, .index = USBDEV_RXFIFO_SIZE_OFFSET,
      });
  // Get the buffer entry that holds the payload
  uint8_t buffer_entry = bitfield_field32_read(
      fifo_entry, (bitfield_field32_t){
                      .mask = USBDEV_RXFIFO_BUFFER_MASK,
                      .index = USBDEV_RXFIFO_BUFFER_OFFSET,
                  });
  // Start a read buffer operation
  buffer_op_start_read(usbdev);
  usbdev->read_buffer_op_state = (dif_usbdev_read_buffer_op_state_t){
      .buffer_entry = buffer_entry, .remaining_bytes = packet->len, .offset = 0,
  };

  return kDifUsbdevRxPacketGetInfoResultOK;
}

dif_usbdev_rx_packet_read_bytes_result_t dif_usbdev_rx_packet_read_bytes(
    dif_usbdev_t *usbdev, uint8_t *dst, size_t dst_len, size_t *bytes_written) {
  if (usbdev == NULL || dst == NULL) {
    return kDifUsbdevRxPacketReadBytesResultBadArg;
  }

  // Make sure that a read buffer operation is in progress
  if (!buffer_op_is_reading(usbdev)) {
    return kDifUsbdevRxPacketReadBytesResultNotReading;
  }
  // bytes_to_copy is the minimum of remaining bytes and `dst_len`
  size_t bytes_to_copy = usbdev->read_buffer_op_state.remaining_bytes;
  if (bytes_to_copy > dst_len) {
    bytes_to_copy = dst_len;
  }
  // Copy payload to buffer
  const uint32_t buffer_addr =
      get_buffer_addr(usbdev->read_buffer_op_state.buffer_entry,
                      usbdev->read_buffer_op_state.offset);
  mmio_region_memcpy_from_mmio32(usbdev->base_addr, buffer_addr, dst,
                                 bytes_to_copy);
  // Update current buffer operation
  usbdev->read_buffer_op_state.offset += bytes_to_copy;
  usbdev->read_buffer_op_state.remaining_bytes -= bytes_to_copy;
  // Check if the entire payload is read
  dif_usbdev_rx_packet_read_bytes_result_t res =
      kDifUsbdevRxPacketReadBytesResultContinue;
  if (usbdev->read_buffer_op_state.remaining_bytes == 0) {
    res = kDifUsbdevRxPacketReadBytesResultOK;
    // Finish read buffer operation
    buffer_op_stop_read(usbdev);
    // Return the buffer to the free buffer pool
    if (!buffer_pool_add(&usbdev->buffer_pool,
                         usbdev->read_buffer_op_state.buffer_entry)) {
      return kDifUsbdevRxPacketReadBytesResultError;
    }
  }

  if (bytes_written != NULL) {
    *bytes_written = bytes_to_copy;
  }

  return res;
}

dif_usbdev_rx_packet_discard_bytes_result_t dif_usbdev_rx_packet_discard_bytes(
    dif_usbdev_t *usbdev) {
  if (usbdev == NULL) {
    return kDifUsbdevRxPacketDiscardBytesResultBadArg;
  }

  // Make sure that a read buffer operation is in progress
  if (!buffer_op_is_reading(usbdev)) {
    return kDifUsbdevRxPacketDiscardBytesResultNotReading;
  }
  // Finish read buffer operation
  buffer_op_stop_read(usbdev);
  // Return the buffer to the free buffer pool
  if (!buffer_pool_add(&usbdev->buffer_pool,
                       usbdev->read_buffer_op_state.buffer_entry)) {
    return kDifUsbdevRxPacketDiscardBytesResultError;
  }

  return kDifUsbdevRxPacketDiscardBytesResultOK;
}

dif_usbdev_tx_packet_write_bytes_result_t dif_usbdev_tx_packet_write_bytes(
    dif_usbdev_t *usbdev, uint8_t endpoint, uint8_t *src, size_t src_len,
    size_t *bytes_written) {
  if (usbdev == NULL || (src_len > 0 && src == NULL) ||
      !is_valid_endpoint(endpoint)) {
    return kDifUsbdevTxPacketWriteBytesResultBadArg;
  }

  // Get tx packet status for the endpoint.
  dif_usbdev_tx_packet_status_t in_packet_status;
  if (dif_usbdev_tx_packet_get_status(usbdev, endpoint, &in_packet_status) !=
      kDifUsbdevOK) {
    return kDifUsbdevTxPacketWriteBytesResultError;
  }

  // Get the configin register offset of the endpoint.
  const uint32_t config_in_reg_offset =
      kEndpointHwInfos[endpoint].config_in_reg_offset;

  uint32_t config_in_val;
  uint8_t buffer_entry;
  uint8_t buffer_len;
  switch (in_packet_status) {
    case kDifUsbdevTxPacketStatusNoPacket: {
      // There is no packet for the endpoint
      // Allocate a new buffer entry
      if (buffer_pool_is_empty(&usbdev->buffer_pool)) {
        return kDifUsbdevTxPacketWriteBytesResultNoBuffers;
      }
      if (!buffer_pool_remove(&usbdev->buffer_pool, &buffer_entry)) {
        return kDifUsbdevTxPacketWriteBytesResultError;
      }
      buffer_len = 0;
      // Start buffer write operation
      buffer_op_start_write(usbdev, endpoint);
      // Update USBDEV_CONFIGIN_X register.
      // Note: Using mask and offset values for the USBDEV_CONFIGIN_0 register
      // for all endpoints because all USBDEV_CONFIGIN_X registers have the same
      // layout.
      uint32_t config_in_val =
          mmio_region_read32(usbdev->base_addr, config_in_reg_offset);
      config_in_val =
          bitfield_field32_write(config_in_val,
                                 (bitfield_field32_t){
                                     .mask = USBDEV_CONFIGIN_0_BUFFER_0_MASK,
                                     .index = USBDEV_CONFIGIN_0_BUFFER_0_OFFSET,
                                 },
                                 buffer_entry);
      config_in_val =
          bitfield_field32_write(config_in_val,
                                 (bitfield_field32_t){
                                     .mask = USBDEV_CONFIGIN_0_SIZE_0_MASK,
                                     .index = USBDEV_CONFIGIN_0_SIZE_0_OFFSET,
                                 },
                                 buffer_len);
      mmio_region_write32(usbdev->base_addr, config_in_reg_offset,
                          config_in_val);
      break;
    }
    case kDifUsbdevTxPacketStatusStillWriting: {
      // Use existing buffer entry
      config_in_val =
          mmio_region_read32(usbdev->base_addr, config_in_reg_offset);
      buffer_entry = bitfield_field32_read(
          config_in_val, (bitfield_field32_t){
                             .mask = USBDEV_CONFIGIN_0_BUFFER_0_MASK,
                             .index = USBDEV_CONFIGIN_0_BUFFER_0_OFFSET,
                         });
      buffer_len = bitfield_field32_read(
          config_in_val, (bitfield_field32_t){
                             .mask = USBDEV_CONFIGIN_0_SIZE_0_MASK,
                             .index = USBDEV_CONFIGIN_0_SIZE_0_OFFSET,
                         });
      break;
    }
    case kDifUsbdevTxPacketStatusPending:
    case kDifUsbdevTxPacketStatusSent:
    case kDifUsbdevTxPacketStatusCancelled:
      // Endpoint already has a packet pending transmission or the status of the
      // last transmission is not read yet.
      return kDifUsbdevTxPacketWriteBytesResultBusy;
    default:
      return kDifUsbdevTxPacketWriteBytesResultError;
  }

  size_t remaining_buffer_space = USBDEV_BUFFER_ENTRY_SIZE_BYTES - buffer_len;
  // `bytes_to_copy` is the minimum of `src_len` and `remaining_buffer_space`.
  size_t bytes_to_copy = src_len;
  if (bytes_to_copy > remaining_buffer_space) {
    bytes_to_copy = remaining_buffer_space;
  }

  // Write bytes to the buffer
  const uint32_t buffer_addr = get_buffer_addr(buffer_entry, buffer_len);
  mmio_region_memcpy_to_mmio32(usbdev->base_addr, buffer_addr, src,
                               bytes_to_copy);

  buffer_len += bytes_to_copy;
  remaining_buffer_space -= bytes_to_copy;

  // Update buffer length in the USBDEV_CONFIGIN_X register.
  mmio_region_nonatomic_set_field32(
      usbdev->base_addr, config_in_reg_offset,
      (bitfield_field32_t){
          .mask = USBDEV_CONFIGIN_0_SIZE_0_MASK,
          .index = USBDEV_CONFIGIN_0_SIZE_0_OFFSET,
      },
      buffer_len);

  if (bytes_written) {
    *bytes_written = bytes_to_copy;
  }

  if (remaining_buffer_space == 0 && bytes_to_copy < src_len) {
    return kDifUsbdevTxPacketWriteBytesResultBufferFull;
  }

  return kDifUsbdevTxPacketWriteBytesResultOK;
}

dif_usbdev_tx_packet_send_result_t dif_usbdev_tx_packet_send(
    dif_usbdev_t *usbdev, uint8_t endpoint) {
  if (usbdev == NULL || !is_valid_endpoint(endpoint)) {
    return kDifUsbdevTxPacketSendResultBadArg;
  }

  // Make sure that there is an active write operation for the endpoint
  if (!buffer_op_is_writing(usbdev, endpoint)) {
    return kDifUsbdevTxPacketSendResultNotWriting;
  }

  // Stop writing to buffer for this endpoint
  buffer_op_stop_write(usbdev, endpoint);
  // Mark the packet as ready for transmission
  mmio_region_nonatomic_set_bit32(
      usbdev->base_addr, kEndpointHwInfos[endpoint].config_in_reg_offset,
      USBDEV_CONFIGIN_0_RDY_0);

  return kDifUsbdevTxPacketSendResultOK;
}

dif_usbdev_result_t dif_usbdev_tx_packet_get_status(
    dif_usbdev_t *usbdev, uint8_t endpoint,
    dif_usbdev_tx_packet_status_t *status) {
  if (usbdev == NULL || status == NULL || !is_valid_endpoint(endpoint)) {
    return kDifUsbdevBadArg;
  }

  // Make sure that there is no active write buffer operation for the endpoint
  if (buffer_op_is_writing(usbdev, endpoint)) {
    *status = kDifUsbdevTxPacketStatusStillWriting;
    return kDifUsbdevOK;
  }

  // Get the configin register offset and bit index of the endpoint
  uint32_t config_in_reg_offset =
      kEndpointHwInfos[endpoint].config_in_reg_offset;
  uint8_t endpoint_bit_index = kEndpointHwInfos[endpoint].bit_index;

  // Read the configin register
  uint32_t config_in_val =
      mmio_region_read32(usbdev->base_addr, config_in_reg_offset);

  // Buffer used by this endpoint
  uint8_t buffer = bitfield_field32_read(
      config_in_val, (bitfield_field32_t){
                         .mask = USBDEV_CONFIGIN_0_BUFFER_0_MASK,
                         .index = USBDEV_CONFIGIN_0_BUFFER_0_OFFSET,
                     });

  // Check the status of the packet
  if (bitfield_field32_read(config_in_val,
                            (bitfield_field32_t){
                                .mask = 1, .index = USBDEV_CONFIGIN_0_RDY_0,
                            })) {
    // Packet is marked as ready to be sent and pending transmission
    *status = kDifUsbdevTxPacketStatusPending;
  } else if (mmio_region_get_bit32(usbdev->base_addr, USBDEV_IN_SENT_REG_OFFSET,
                                   endpoint_bit_index)) {
    // Packet was sent successfully
    // Clear IN_SENT bit (rw1c)
    mmio_region_write_only_set_bit32(
        usbdev->base_addr, USBDEV_IN_SENT_REG_OFFSET, endpoint_bit_index);
    // Return the buffer back to the free buffer pool
    if (!buffer_pool_add(&usbdev->buffer_pool, buffer)) {
      return kDifUsbdevError;
    }
    *status = kDifUsbdevTxPacketStatusSent;
  } else if (bitfield_field32_read(
                 config_in_val,
                 (bitfield_field32_t){
                     .mask = 1, .index = USBDEV_CONFIGIN_0_PEND_0,
                 })) {
    // Canceled due to an IN SETUP packet
    // Clear pending bit (rw1c)
    mmio_region_write_only_set_bit32(usbdev->base_addr, config_in_reg_offset,
                                     USBDEV_CONFIGIN_0_PEND_0);
    // Return the buffer back to the free buffer pool
    if (!buffer_pool_add(&usbdev->buffer_pool, buffer)) {
      return kDifUsbdevError;
    }
    *status = kDifUsbdevTxPacketStatusCancelled;
  } else {
    // No packet has been queued for this endpoint
    *status = kDifUsbdevTxPacketStatusNoPacket;
  }

  return kDifUsbdevOK;
}

dif_usbdev_result_t dif_usbdev_address_set(dif_usbdev_t *usbdev, uint8_t addr) {
  if (usbdev == NULL) {
    return kDifUsbdevBadArg;
  }

  mmio_region_nonatomic_set_field32(
      usbdev->base_addr, USBDEV_USBCTRL_REG_OFFSET,
      (bitfield_field32_t){
          .mask = USBDEV_USBCTRL_DEVICE_ADDRESS_MASK,
          .index = USBDEV_USBCTRL_DEVICE_ADDRESS_OFFSET,
      },
      addr);

  return kDifUsbdevOK;
}

dif_usbdev_result_t dif_usbdev_address_get(dif_usbdev_t *usbdev,
                                           uint8_t *addr) {
  if (usbdev == NULL || addr == NULL) {
    return kDifUsbdevBadArg;
  }

  // Note: Size of address is 7 bits.
  *addr = mmio_region_read_mask32(usbdev->base_addr, USBDEV_USBCTRL_REG_OFFSET,
                                  USBDEV_USBCTRL_DEVICE_ADDRESS_MASK,
                                  USBDEV_USBCTRL_DEVICE_ADDRESS_OFFSET);

  return kDifUsbdevOK;
}

dif_usbdev_result_t dif_usbdev_status_get_frame(dif_usbdev_t *usbdev,
                                                uint16_t *frame_index) {
  if (usbdev == NULL || frame_index == NULL) {
    return kDifUsbdevBadArg;
  }

  // Note: size of frame index is 11 bits.
  *frame_index = mmio_region_read_mask32(
      usbdev->base_addr, USBDEV_USBSTAT_REG_OFFSET, USBDEV_USBSTAT_FRAME_MASK,
      USBDEV_USBSTAT_FRAME_OFFSET);

  return kDifUsbdevOK;
}

dif_usbdev_result_t dif_usbdev_status_get_host_lost(dif_usbdev_t *usbdev,
                                                    bool *host_lost) {
  if (usbdev == NULL || host_lost == NULL) {
    return kDifUsbdevBadArg;
  }

  *host_lost = mmio_region_get_bit32(
      usbdev->base_addr, USBDEV_USBSTAT_REG_OFFSET, USBDEV_USBSTAT_HOST_LOST);

  return kDifUsbdevOK;
}

dif_usbdev_result_t dif_usbdev_status_get_link_state(
    dif_usbdev_t *usbdev, dif_usbdev_link_state_t *link_state) {
  if (usbdev == NULL || link_state == NULL) {
    return kDifUsbdevBadArg;
  }

  uint32_t val = mmio_region_read_mask32(
      usbdev->base_addr, USBDEV_USBSTAT_REG_OFFSET,
      USBDEV_USBSTAT_LINK_STATE_MASK, USBDEV_USBSTAT_LINK_STATE_OFFSET);

  switch (val) {
    case USBDEV_USBSTAT_LINK_STATE_DISCONNECT:
      *link_state = kDifUsbdevLinkStateDisconnected;
      break;
    case USBDEV_USBSTAT_LINK_STATE_POWERED:
      *link_state = kDifUsbdevLinkStatePowered;
      break;
    case USBDEV_USBSTAT_LINK_STATE_POWERED_SUSPEND:
      *link_state = kDifUsbdevLinkStatePoweredSuspend;
      break;
    case USBDEV_USBSTAT_LINK_STATE_ACTIVE:
      *link_state = kDifUsbdevLinkStateActive;
      break;
    case USBDEV_USBSTAT_LINK_STATE_SUSPEND:
      *link_state = kDifUsbdevLinkStateSuspend;
      break;
    default:
      return kDifUsbdevError;
  }

  return kDifUsbdevOK;
}

dif_usbdev_result_t dif_usbdev_status_get_sense(dif_usbdev_t *usbdev,
                                                bool *sense) {
  if (usbdev == NULL || sense == NULL) {
    return kDifUsbdevBadArg;
  }

  *sense = mmio_region_get_bit32(usbdev->base_addr, USBDEV_USBSTAT_REG_OFFSET,
                                 USBDEV_USBSTAT_SENSE);

  return kDifUsbdevOK;
}

dif_usbdev_result_t dif_usbdev_status_get_available_fifo_depth(
    dif_usbdev_t *usbdev, uint8_t *depth) {
  if (usbdev == NULL || depth == NULL) {
    return kDifUsbdevBadArg;
  }

  // Note: Size of available FIFO depth is 3 bits.
  *depth = mmio_region_read_mask32(usbdev->base_addr, USBDEV_USBSTAT_REG_OFFSET,
                                   USBDEV_USBSTAT_AV_DEPTH_MASK,
                                   USBDEV_USBSTAT_AV_DEPTH_OFFSET);

  return kDifUsbdevOK;
}

dif_usbdev_result_t dif_usbdev_status_get_available_fifo_full(
    dif_usbdev_t *usbdev, bool *is_full) {
  if (usbdev == NULL || is_full == NULL) {
    return kDifUsbdevBadArg;
  }

  *is_full = mmio_region_get_bit32(usbdev->base_addr, USBDEV_USBSTAT_REG_OFFSET,
                                   USBDEV_USBSTAT_AV_FULL);

  return kDifUsbdevOK;
}

dif_usbdev_result_t dif_usbdev_status_get_rx_fifo_depth(dif_usbdev_t *usbdev,
                                                        uint8_t *depth) {
  if (usbdev == NULL || depth == NULL) {
    return kDifUsbdevBadArg;
  }

  // Note: Size of RX FIFO depth is 3 bits.
  *depth = mmio_region_read_mask32(usbdev->base_addr, USBDEV_USBSTAT_REG_OFFSET,
                                   USBDEV_USBSTAT_RX_DEPTH_MASK,
                                   USBDEV_USBSTAT_RX_DEPTH_OFFSET);

  return kDifUsbdevOK;
}

dif_usbdev_result_t dif_usbdev_status_get_rx_fifo_empty(dif_usbdev_t *usbdev,
                                                        bool *is_full) {
  if (usbdev == NULL || is_full == NULL) {
    return kDifUsbdevBadArg;
  }

  *is_full = mmio_region_get_bit32(usbdev->base_addr, USBDEV_USBSTAT_REG_OFFSET,
                                   USBDEV_USBSTAT_RX_EMPTY);

  return kDifUsbdevOK;
}

dif_usbdev_result_t dif_usbdev_irq_enable(dif_usbdev_t *usbdev,
                                          dif_usbdev_irq_t irq,
                                          dif_usbdev_toggle_t state) {
  if (usbdev == NULL || !is_valid_irq(irq) || !is_valid_toggle(state)) {
    return kDifUsbdevBadArg;
  }

  if (state == kDifUsbdevToggleEnable) {
    mmio_region_nonatomic_set_bit32(usbdev->base_addr,
                                    USBDEV_INTR_ENABLE_REG_OFFSET,
                                    kIrqEnumToBitIndex[irq]);
  } else {
    mmio_region_nonatomic_clear_bit32(usbdev->base_addr,
                                      USBDEV_INTR_ENABLE_REG_OFFSET,
                                      kIrqEnumToBitIndex[irq]);
  }

  return kDifUsbdevOK;
}

dif_usbdev_result_t dif_usbdev_irq_get(dif_usbdev_t *usbdev,
                                       dif_usbdev_irq_t irq, bool *state) {
  if (usbdev == NULL || state == NULL || !is_valid_irq(irq)) {
    return kDifUsbdevBadArg;
  }

  *state = mmio_region_get_bit32(
      usbdev->base_addr, USBDEV_INTR_STATE_REG_OFFSET, kIrqEnumToBitIndex[irq]);

  return kDifUsbdevOK;
}

dif_usbdev_result_t dif_usbdev_irq_clear(dif_usbdev_t *usbdev,
                                         dif_usbdev_irq_t irq) {
  if (usbdev == NULL || !is_valid_irq(irq)) {
    return kDifUsbdevBadArg;
  }

  mmio_region_write_only_set_bit32(
      usbdev->base_addr, USBDEV_INTR_STATE_REG_OFFSET, kIrqEnumToBitIndex[irq]);

  return kDifUsbdevOK;
}

dif_usbdev_result_t dif_usbdev_irq_clear_all(dif_usbdev_t *usbdev) {
  if (usbdev == NULL) {
    return kDifUsbdevBadArg;
  }

  mmio_region_write32(usbdev->base_addr, USBDEV_INTR_STATE_REG_OFFSET,
                      UINT32_MAX);

  return kDifUsbdevOK;
}

dif_usbdev_result_t dif_usbdev_irq_disable_all(dif_usbdev_t *usbdev,
                                               uint32_t *cur_config) {
  if (usbdev == NULL) {
    return kDifUsbdevBadArg;
  }

  if (cur_config != NULL) {
    *cur_config =
        mmio_region_read32(usbdev->base_addr, USBDEV_INTR_ENABLE_REG_OFFSET);
  }

  mmio_region_write32(usbdev->base_addr, USBDEV_INTR_ENABLE_REG_OFFSET, 0);

  return kDifUsbdevOK;
}

dif_usbdev_result_t dif_usbdev_irq_restore(dif_usbdev_t *usbdev,
                                           uint32_t new_config) {
  if (usbdev == NULL) {
    return kDifUsbdevBadArg;
  }

  mmio_region_write32(usbdev->base_addr, USBDEV_INTR_ENABLE_REG_OFFSET,
                      new_config);

  return kDifUsbdevOK;
}

dif_usbdev_result_t dif_usbdev_irq_test(dif_usbdev_t *usbdev,
                                        dif_usbdev_irq_t irq) {
  if (usbdev == NULL || !is_valid_irq(irq)) {
    return kDifUsbdevBadArg;
  }

  mmio_region_write_only_set_bit32(
      usbdev->base_addr, USBDEV_INTR_TEST_REG_OFFSET, kIrqEnumToBitIndex[irq]);

  return kDifUsbdevOK;
}
