// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/dif/dif_usbdev.h"

#include <assert.h>

#include "sw/device/lib/base/bitfield.h"

#include "usbdev_regs.h"  // Generated.

/**
 * Definition in the header file (and probably other places) must be updated if
 * there is a hardware change.
 */
static_assert(USBDEV_NUM_ENDPOINTS == USBDEV_PARAM_N_ENDPOINTS,
              "Mismatch in number of endpoints");

/**
 * Max packet size is equal to the size of device buffers.
 */
#define USBDEV_BUFFER_ENTRY_SIZE_BYTES USBDEV_MAX_PACKET_SIZE

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
         .bit_index = USBDEV_IN_SENT_SENT_##N##_BIT}

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
 * Static functions for the free buffer pool.
 */

/**
 * Checks if a buffer pool is full.
 *
 * A buffer pool is full if it contains `USBDEV_NUM_BUFFERS` buffers.
 *
 * @param pool A buffer pool.
 * @return `true` if the buffer pool if full, `false` otherwise.
 */
OT_WARN_UNUSED_RESULT
static bool buffer_pool_is_full(dif_usbdev_buffer_pool_t *pool) {
  return pool->top == BUFFER_POOL_FULL;
}

/**
 * Checks if a buffer pool is empty.
 *
 * @param pool A buffer pool.
 * @return `true` if the buffer pool is empty, `false` otherwise.
 */
OT_WARN_UNUSED_RESULT
static bool buffer_pool_is_empty(dif_usbdev_buffer_pool_t *pool) {
  return pool->top == BUFFER_POOL_EMPTY;
}

/**
 * Checks if a buffer id is valid.
 *
 * A buffer id is valid if it is less than `USBDEV_NUM_BUFFERS`.
 *
 * @param buffer_id A buffer id.
 * @return `true` if `buffer_id` is valid, `false` otherwise.
 */
OT_WARN_UNUSED_RESULT
static bool buffer_pool_is_valid_buffer_id(uint8_t buffer_id) {
  return buffer_id < USBDEV_NUM_BUFFERS;
}

/**
 * Adds a buffer to a buffer pool.
 *
 * @param pool A buffer pool.
 * @param buffer_id A buffer id.
 * @return `true` if the operation was successful, `false` otherwise.
 */
OT_WARN_UNUSED_RESULT
static bool buffer_pool_add(dif_usbdev_buffer_pool_t *pool, uint8_t buffer_id) {
  if (buffer_pool_is_full(pool) || !buffer_pool_is_valid_buffer_id(buffer_id)) {
    return false;
  }

  ++pool->top;
  pool->buffers[pool->top] = buffer_id;

  return true;
}

/**
 * Removes a buffer from a buffer pool.
 *
 * @param pool A buffer pool.
 * @param buffer_id A buffer id.
 * @return `true` if the operation was successful, `false` otherwise.
 */
OT_WARN_UNUSED_RESULT
static bool buffer_pool_remove(dif_usbdev_buffer_pool_t *pool,
                               uint8_t *buffer_id) {
  if (buffer_pool_is_empty(pool) || buffer_id == NULL) {
    return false;
  }

  *buffer_id = pool->buffers[pool->top];
  --pool->top;

  return true;
}

/**
 * Initializes the buffer pool.
 *
 * At the end of this operation, the buffer pool contains `USBDEV_NUM_BUFFERS`
 * buffers.
 *
 * @param pool A buffer pool.
 * @return `true` if the operation was successful, `false` otherwise.
 */
OT_WARN_UNUSED_RESULT
static bool buffer_pool_init(dif_usbdev_buffer_pool_t *pool) {
  // Start with an empty pool
  pool->top = -1;

  // Add all buffers
  for (uint8_t i = 0; i < USBDEV_NUM_BUFFERS; ++i) {
    if (!buffer_pool_add(pool, i)) {
      return false;
    }
  }

  return true;
}

/**
 * Utility functions
 */

/**
 * Checks if the given value is a valid endpoint number.
 */
OT_WARN_UNUSED_RESULT
static bool is_valid_endpoint(uint8_t endpoint_number) {
  return endpoint_number < USBDEV_NUM_ENDPOINTS;
}

/**
 * Enables/disables the functionality controlled by the register at `reg_offset`
 * for an endpoint.
 */
OT_WARN_UNUSED_RESULT
static dif_result_t endpoint_functionality_enable(const dif_usbdev_t *usbdev,
                                                  uint32_t reg_offset,
                                                  uint8_t endpoint,
                                                  dif_toggle_t new_state) {
  if (usbdev == NULL || !is_valid_endpoint(endpoint) ||
      !dif_is_valid_toggle(new_state)) {
    return kDifBadArg;
  }

  uint32_t reg_val =
      mmio_region_read32(usbdev->base_addr, (ptrdiff_t)reg_offset);
  reg_val = bitfield_bit32_write(reg_val, kEndpointHwInfos[endpoint].bit_index,
                                 dif_toggle_to_bool(new_state));
  mmio_region_write32(usbdev->base_addr, (ptrdiff_t)reg_offset, reg_val);
  return kDifOk;
}

/**
 * Returns the address that corresponds to the given buffer and offset
 * into that buffer.
 */
OT_WARN_UNUSED_RESULT
static uint32_t get_buffer_addr(uint8_t buffer_id, size_t offset) {
  return USBDEV_BUFFER_REG_OFFSET +
         (buffer_id * USBDEV_BUFFER_ENTRY_SIZE_BYTES) + offset;
}

/**
 * USBDEV DIF library functions.
 */

dif_result_t dif_usbdev_configure(const dif_usbdev_t *usbdev,
                                  dif_usbdev_buffer_pool_t *buffer_pool,
                                  dif_usbdev_config_t config) {
  if (usbdev == NULL || buffer_pool == NULL) {
    return kDifBadArg;
  }

  // Configure the free buffer pool.
  if (!buffer_pool_init(buffer_pool)) {
    return kDifError;
  }

  // Check enum fields.
  if (!dif_is_valid_toggle(config.have_differential_receiver) ||
      !dif_is_valid_toggle(config.use_tx_d_se0) ||
      !dif_is_valid_toggle(config.single_bit_eop) ||
      !dif_is_valid_toggle(config.pin_flip) ||
      !dif_is_valid_toggle(config.clock_sync_signals)) {
    return kDifBadArg;
  }

  // Determine the value of the PHY_CONFIG register.
  uint32_t phy_config_val = 0;
  phy_config_val = bitfield_bit32_write(
      phy_config_val, USBDEV_PHY_CONFIG_USE_DIFF_RCVR_BIT,
      dif_toggle_to_bool(config.have_differential_receiver));
  phy_config_val =
      bitfield_bit32_write(phy_config_val, USBDEV_PHY_CONFIG_TX_USE_D_SE0_BIT,
                           dif_toggle_to_bool(config.use_tx_d_se0));
  phy_config_val =
      bitfield_bit32_write(phy_config_val, USBDEV_PHY_CONFIG_EOP_SINGLE_BIT_BIT,
                           dif_toggle_to_bool(config.single_bit_eop));
  phy_config_val =
      bitfield_bit32_write(phy_config_val, USBDEV_PHY_CONFIG_PINFLIP_BIT,
                           dif_toggle_to_bool(config.pin_flip));
  phy_config_val = bitfield_bit32_write(
      phy_config_val, USBDEV_PHY_CONFIG_USB_REF_DISABLE_BIT,
      !dif_toggle_to_bool(config.clock_sync_signals));

  // Write configuration to PHY_CONFIG register
  mmio_region_write32(usbdev->base_addr, USBDEV_PHY_CONFIG_REG_OFFSET,
                      phy_config_val);

  return kDifOk;
}

dif_result_t dif_usbdev_fill_available_fifo(
    const dif_usbdev_t *usbdev, dif_usbdev_buffer_pool_t *buffer_pool) {
  if (usbdev == NULL || buffer_pool == NULL) {
    return kDifBadArg;
  }

  // Remove buffers from the pool and write them to the AV FIFO until it is full
  while (true) {
    uint32_t status =
        mmio_region_read32(usbdev->base_addr, USBDEV_USBSTAT_REG_OFFSET);
    bool av_full = bitfield_bit32_read(status, USBDEV_USBSTAT_AV_FULL_BIT);
    if (av_full || buffer_pool_is_empty(buffer_pool)) {
      break;
    }
    uint8_t buffer_id;
    if (!buffer_pool_remove(buffer_pool, &buffer_id)) {
      return kDifError;
    }
    uint32_t reg_val =
        bitfield_field32_write(0, USBDEV_AVBUFFER_BUFFER_FIELD, buffer_id);
    mmio_region_write32(usbdev->base_addr, USBDEV_AVBUFFER_REG_OFFSET, reg_val);
  }

  return kDifOk;
}

dif_result_t dif_usbdev_endpoint_setup_enable(const dif_usbdev_t *usbdev,
                                              uint8_t endpoint,
                                              dif_toggle_t new_state) {
  return endpoint_functionality_enable(usbdev, USBDEV_RXENABLE_SETUP_REG_OFFSET,
                                       endpoint, new_state);
}

dif_result_t dif_usbdev_endpoint_out_enable(const dif_usbdev_t *usbdev,
                                            uint8_t endpoint,
                                            dif_toggle_t new_state) {
  return endpoint_functionality_enable(usbdev, USBDEV_RXENABLE_OUT_REG_OFFSET,
                                       endpoint, new_state);
}

dif_result_t dif_usbdev_endpoint_set_nak_out_enable(const dif_usbdev_t *usbdev,
                                                    uint8_t endpoint,
                                                    dif_toggle_t new_state) {
  return endpoint_functionality_enable(usbdev, USBDEV_SET_NAK_OUT_REG_OFFSET,
                                       endpoint, new_state);
}

dif_result_t dif_usbdev_endpoint_stall_enable(const dif_usbdev_t *usbdev,
                                              dif_usbdev_endpoint_id_t endpoint,
                                              dif_toggle_t new_state) {
  if (endpoint.direction == USBDEV_ENDPOINT_DIR_IN) {
    return endpoint_functionality_enable(usbdev, USBDEV_IN_STALL_REG_OFFSET,
                                         endpoint.number, new_state);
  } else {
    return endpoint_functionality_enable(usbdev, USBDEV_OUT_STALL_REG_OFFSET,
                                         endpoint.number, new_state);
  }
}

dif_result_t dif_usbdev_endpoint_stall_get(const dif_usbdev_t *usbdev,
                                           dif_usbdev_endpoint_id_t endpoint,
                                           bool *state) {
  if (usbdev == NULL || state == NULL || !is_valid_endpoint(endpoint.number)) {
    return kDifBadArg;
  }

  ptrdiff_t reg_offset = endpoint.direction == USBDEV_ENDPOINT_DIR_IN
                             ? USBDEV_IN_STALL_REG_OFFSET
                             : USBDEV_OUT_STALL_REG_OFFSET;
  uint32_t reg_val = mmio_region_read32(usbdev->base_addr, reg_offset);
  *state =
      bitfield_bit32_read(reg_val, kEndpointHwInfos[endpoint.number].bit_index);

  return kDifOk;
}

dif_result_t dif_usbdev_endpoint_iso_enable(const dif_usbdev_t *usbdev,
                                            dif_usbdev_endpoint_id_t endpoint,
                                            dif_toggle_t new_state) {
  if (endpoint.direction == USBDEV_ENDPOINT_DIR_IN) {
    return endpoint_functionality_enable(usbdev, USBDEV_IN_ISO_REG_OFFSET,
                                         endpoint.number, new_state);
  } else {
    return endpoint_functionality_enable(usbdev, USBDEV_OUT_ISO_REG_OFFSET,
                                         endpoint.number, new_state);
  }
}

dif_result_t dif_usbdev_endpoint_enable(const dif_usbdev_t *usbdev,
                                        dif_usbdev_endpoint_id_t endpoint,
                                        dif_toggle_t new_state) {
  if (endpoint.direction == USBDEV_ENDPOINT_DIR_IN) {
    return endpoint_functionality_enable(usbdev, USBDEV_EP_IN_ENABLE_REG_OFFSET,
                                         endpoint.number, new_state);
  } else {
    return endpoint_functionality_enable(
        usbdev, USBDEV_EP_OUT_ENABLE_REG_OFFSET, endpoint.number, new_state);
  }
  return kDifOk;
}

dif_result_t dif_usbdev_interface_enable(const dif_usbdev_t *usbdev,
                                         dif_toggle_t new_state) {
  if (usbdev == NULL || !dif_is_valid_toggle(new_state)) {
    return kDifBadArg;
  }

  uint32_t reg_val =
      mmio_region_read32(usbdev->base_addr, USBDEV_USBCTRL_REG_OFFSET);
  reg_val = bitfield_bit32_write(reg_val, USBDEV_USBCTRL_ENABLE_BIT,
                                 dif_toggle_to_bool(new_state));
  mmio_region_write32(usbdev->base_addr, USBDEV_USBCTRL_REG_OFFSET, reg_val);

  return kDifOk;
}

dif_result_t dif_usbdev_recv(const dif_usbdev_t *usbdev,
                             dif_usbdev_rx_packet_info_t *info,
                             dif_usbdev_buffer_t *buffer) {
  if (usbdev == NULL || info == NULL || buffer == NULL) {
    return kDifBadArg;
  }

  // Check if the RX FIFO is empty
  uint32_t fifo_status =
      mmio_region_read32(usbdev->base_addr, USBDEV_USBSTAT_REG_OFFSET);
  if (bitfield_bit32_read(fifo_status, USBDEV_USBSTAT_RX_EMPTY_BIT)) {
    return kDifUnavailable;
  }

  // Read fifo entry
  const uint32_t fifo_entry =
      mmio_region_read32(usbdev->base_addr, USBDEV_RXFIFO_REG_OFFSET);
  // Init packet info
  *info = (dif_usbdev_rx_packet_info_t){
      .endpoint =
          (uint8_t)bitfield_field32_read(fifo_entry, USBDEV_RXFIFO_EP_FIELD),
      .is_setup = bitfield_bit32_read(fifo_entry, USBDEV_RXFIFO_SETUP_BIT),
      .length =
          (uint8_t)bitfield_field32_read(fifo_entry, USBDEV_RXFIFO_SIZE_FIELD),
  };
  // Init buffer struct
  *buffer = (dif_usbdev_buffer_t){
      .id = (uint8_t)bitfield_field32_read(fifo_entry,
                                           USBDEV_RXFIFO_BUFFER_FIELD),
      .offset = 0,
      .remaining_bytes = info->length,
      .type = kDifUsbdevBufferTypeRead,
  };

  return kDifOk;
}

dif_result_t dif_usbdev_buffer_request(const dif_usbdev_t *usbdev,
                                       dif_usbdev_buffer_pool_t *buffer_pool,
                                       dif_usbdev_buffer_t *buffer) {
  if (usbdev == NULL || buffer_pool == NULL || buffer == NULL) {
    return kDifBadArg;
  }

  if (buffer_pool_is_empty(buffer_pool)) {
    return kDifUnavailable;
  }

  uint8_t buffer_id;
  if (!buffer_pool_remove(buffer_pool, &buffer_id)) {
    return kDifError;
  }

  *buffer = (dif_usbdev_buffer_t){
      .id = buffer_id,
      .offset = 0,
      .remaining_bytes = USBDEV_BUFFER_ENTRY_SIZE_BYTES,
      .type = kDifUsbdevBufferTypeWrite,
  };

  return kDifOk;
}

dif_result_t dif_usbdev_buffer_return(const dif_usbdev_t *usbdev,
                                      dif_usbdev_buffer_pool_t *buffer_pool,
                                      dif_usbdev_buffer_t *buffer) {
  if (usbdev == NULL || buffer_pool == NULL || buffer == NULL) {
    return kDifBadArg;
  }

  switch (buffer->type) {
    case kDifUsbdevBufferTypeRead:
    case kDifUsbdevBufferTypeWrite:
      // Return the buffer to the free buffer pool
      if (!buffer_pool_add(buffer_pool, buffer->id)) {
        return kDifError;
      }
      // Mark the buffer as stale
      buffer->type = kDifUsbdevBufferTypeStale;
      return kDifOk;
    default:
      return kDifBadArg;
  }
}

dif_result_t dif_usbdev_buffer_read(const dif_usbdev_t *usbdev,
                                    dif_usbdev_buffer_pool_t *buffer_pool,
                                    dif_usbdev_buffer_t *buffer, uint8_t *dst,
                                    size_t dst_len, size_t *bytes_written) {
  if (usbdev == NULL || buffer_pool == NULL || buffer == NULL ||
      buffer->type != kDifUsbdevBufferTypeRead || dst == NULL) {
    return kDifBadArg;
  }

  // bytes_to_copy is the minimum of remaining_bytes and dst_len
  size_t bytes_to_copy = buffer->remaining_bytes;
  if (bytes_to_copy > dst_len) {
    bytes_to_copy = dst_len;
  }
  // Copy from buffer to dst
  const uint32_t buffer_addr = get_buffer_addr(buffer->id, buffer->offset);
  mmio_region_memcpy_from_mmio32(usbdev->base_addr, buffer_addr, dst,
                                 bytes_to_copy);
  // Update buffer state
  buffer->offset += bytes_to_copy;
  buffer->remaining_bytes -= bytes_to_copy;

  if (bytes_written != NULL) {
    *bytes_written = bytes_to_copy;
  }

  // Check if there are any remaining bytes
  if (buffer->remaining_bytes > 0) {
    return kDifOk;
  }

  // Return the buffer to the free buffer pool
  if (!buffer_pool_add(buffer_pool, buffer->id)) {
    return kDifError;
  }

  // Mark the buffer as stale
  buffer->type = kDifUsbdevBufferTypeStale;
  return kDifOk;
}

dif_result_t dif_usbdev_buffer_write(const dif_usbdev_t *usbdev,
                                     dif_usbdev_buffer_t *buffer,
                                     const uint8_t *src, size_t src_len,
                                     size_t *bytes_written) {
  if (usbdev == NULL || buffer == NULL ||
      buffer->type != kDifUsbdevBufferTypeWrite || src == NULL) {
    return kDifBadArg;
  }

  // bytes_to_copy is the minimum of remaining_bytes and src_len.
  size_t bytes_to_copy = buffer->remaining_bytes;
  if (bytes_to_copy > src_len) {
    bytes_to_copy = src_len;
  }

  // Write bytes to the buffer
  uint32_t buffer_addr = get_buffer_addr(buffer->id, buffer->offset);
  mmio_region_memcpy_to_mmio32(usbdev->base_addr, buffer_addr, src,
                               bytes_to_copy);

  buffer->offset += bytes_to_copy;
  buffer->remaining_bytes -= bytes_to_copy;

  if (bytes_written) {
    *bytes_written = bytes_to_copy;
  }

  if (buffer->remaining_bytes == 0 && bytes_to_copy < src_len) {
    return kDifError;
  }

  return kDifOk;
}

dif_result_t dif_usbdev_send(const dif_usbdev_t *usbdev, uint8_t endpoint,
                             dif_usbdev_buffer_t *buffer) {
  if (usbdev == NULL || !is_valid_endpoint(endpoint) || buffer == NULL ||
      buffer->type != kDifUsbdevBufferTypeWrite) {
    return kDifBadArg;
  }

  // Get the configin register offset of the endpoint.
  const uint32_t config_in_reg_offset =
      kEndpointHwInfos[endpoint].config_in_reg_offset;

  // Configure USBDEV_CONFIGINX register.
  // Note: Using mask and offset values for the USBDEV_CONFIGIN0 register
  // for all endpoints because all USBDEV_CONFIGINX registers have the same
  // layout.
  uint32_t config_in_val = 0;
  config_in_val = bitfield_field32_write(
      config_in_val, USBDEV_CONFIGIN_0_BUFFER_0_FIELD, buffer->id);
  config_in_val = bitfield_field32_write(
      config_in_val, USBDEV_CONFIGIN_0_SIZE_0_FIELD, buffer->offset);
  mmio_region_write32(usbdev->base_addr, (ptrdiff_t)config_in_reg_offset,
                      config_in_val);

  // Mark the packet as ready for transmission
  config_in_val =
      bitfield_bit32_write(config_in_val, USBDEV_CONFIGIN_0_RDY_0_BIT, true);
  mmio_region_write32(usbdev->base_addr, (ptrdiff_t)config_in_reg_offset,
                      config_in_val);

  // Mark the buffer as stale. It will be returned to the free buffer pool
  // in dif_usbdev_get_tx_status once transmission is complete.
  buffer->type = kDifUsbdevBufferTypeStale;

  return kDifOk;
}

dif_result_t dif_usbdev_get_tx_sent(const dif_usbdev_t *usbdev,
                                    uint16_t *sent) {
  if (usbdev == NULL || sent == NULL) {
    return kDifBadArg;
  }
  *sent = (uint16_t)mmio_region_read32(usbdev->base_addr,
                                       USBDEV_IN_SENT_REG_OFFSET);
  return kDifOk;
}

dif_result_t dif_usbdev_clear_tx_status(const dif_usbdev_t *usbdev,
                                        dif_usbdev_buffer_pool_t *buffer_pool,
                                        uint8_t endpoint) {
  if (usbdev == NULL || buffer_pool == NULL || !is_valid_endpoint(endpoint)) {
    return kDifBadArg;
  }
  // Get the configin register offset and bit index of the endpoint.
  uint32_t config_in_reg_offset =
      kEndpointHwInfos[endpoint].config_in_reg_offset;
  uint32_t config_in_reg_val =
      mmio_region_read32(usbdev->base_addr, (ptrdiff_t)config_in_reg_offset);
  uint8_t buffer = (uint8_t)bitfield_field32_read(
      config_in_reg_val, USBDEV_CONFIGIN_0_BUFFER_0_FIELD);

  mmio_region_write32(usbdev->base_addr, (ptrdiff_t)config_in_reg_offset,
                      1u << USBDEV_CONFIGIN_0_PEND_0_BIT);
  // Clear IN_SENT bit (rw1c).
  mmio_region_write32(usbdev->base_addr, USBDEV_IN_SENT_REG_OFFSET,
                      1u << endpoint);
  // Return the buffer back to the free buffer pool.
  if (!buffer_pool_add(buffer_pool, buffer)) {
    return kDifError;
  }
  return kDifOk;
}

dif_result_t dif_usbdev_get_tx_status(const dif_usbdev_t *usbdev,
                                      uint8_t endpoint,
                                      dif_usbdev_tx_status_t *status) {
  if (usbdev == NULL || status == NULL || !is_valid_endpoint(endpoint)) {
    return kDifBadArg;
  }

  // Get the configin register offset and bit index of the endpoint.
  uint32_t config_in_reg_offset =
      kEndpointHwInfos[endpoint].config_in_reg_offset;
  uint8_t endpoint_bit_index = kEndpointHwInfos[endpoint].bit_index;

  // Read the configin register.
  uint32_t config_in_val =
      mmio_region_read32(usbdev->base_addr, (ptrdiff_t)config_in_reg_offset);

  // Check the status of the packet.
  if (bitfield_bit32_read(config_in_val, USBDEV_CONFIGIN_0_RDY_0_BIT)) {
    // Packet is marked as ready to be sent and pending transmission.
    *status = kDifUsbdevTxStatusPending;
  } else if (bitfield_bit32_read(mmio_region_read32(usbdev->base_addr,
                                                    USBDEV_IN_SENT_REG_OFFSET),
                                 endpoint_bit_index)) {
    // Packet was sent successfully.
    *status = kDifUsbdevTxStatusSent;
  } else if (bitfield_bit32_read(config_in_val, USBDEV_CONFIGIN_0_PEND_0_BIT)) {
    // Canceled due to an IN SETUP packet or link reset.
    *status = kDifUsbdevTxStatusCancelled;
  } else {
    // No packet has been queued for this endpoint.
    *status = kDifUsbdevTxStatusNoPacket;
  }

  return kDifOk;
}

dif_result_t dif_usbdev_address_set(const dif_usbdev_t *usbdev, uint8_t addr) {
  if (usbdev == NULL) {
    return kDifBadArg;
  }

  uint32_t reg_val =
      mmio_region_read32(usbdev->base_addr, USBDEV_USBCTRL_REG_OFFSET);
  reg_val = bitfield_field32_write(reg_val, USBDEV_USBCTRL_DEVICE_ADDRESS_FIELD,
                                   addr);
  mmio_region_write32(usbdev->base_addr, USBDEV_USBCTRL_REG_OFFSET, reg_val);

  return kDifOk;
}

dif_result_t dif_usbdev_address_get(const dif_usbdev_t *usbdev, uint8_t *addr) {
  if (usbdev == NULL || addr == NULL) {
    return kDifBadArg;
  }

  uint32_t reg_val =
      mmio_region_read32(usbdev->base_addr, USBDEV_USBCTRL_REG_OFFSET);
  // Note: Size of address is 7 bits.
  *addr = (uint8_t)bitfield_field32_read(reg_val,
                                         USBDEV_USBCTRL_DEVICE_ADDRESS_FIELD);

  return kDifOk;
}

dif_result_t dif_usbdev_clear_data_toggle(const dif_usbdev_t *usbdev,
                                          uint8_t endpoint) {
  if (usbdev == NULL) {
    return kDifBadArg;
  }
  mmio_region_write32(usbdev->base_addr, USBDEV_DATA_TOGGLE_CLEAR_REG_OFFSET,
                      1u << endpoint);
  return kDifOk;
}

dif_result_t dif_usbdev_status_get_frame(const dif_usbdev_t *usbdev,
                                         uint16_t *frame_index) {
  if (usbdev == NULL || frame_index == NULL) {
    return kDifBadArg;
  }

  uint32_t reg_val =
      mmio_region_read32(usbdev->base_addr, USBDEV_USBSTAT_REG_OFFSET);
  // Note: size of frame index is 11 bits.
  *frame_index =
      (uint8_t)bitfield_field32_read(reg_val, USBDEV_USBSTAT_FRAME_FIELD);

  return kDifOk;
}

dif_result_t dif_usbdev_status_get_host_lost(const dif_usbdev_t *usbdev,
                                             bool *host_lost) {
  if (usbdev == NULL || host_lost == NULL) {
    return kDifBadArg;
  }

  *host_lost =
      mmio_region_get_bit32(usbdev->base_addr, USBDEV_USBSTAT_REG_OFFSET,
                            USBDEV_USBSTAT_HOST_LOST_BIT);

  return kDifOk;
}

dif_result_t dif_usbdev_status_get_link_state(
    const dif_usbdev_t *usbdev, dif_usbdev_link_state_t *link_state) {
  if (usbdev == NULL || link_state == NULL) {
    return kDifBadArg;
  }

  uint32_t val =
      mmio_region_read32(usbdev->base_addr, USBDEV_USBSTAT_REG_OFFSET);
  val = bitfield_field32_read(val, USBDEV_USBSTAT_LINK_STATE_FIELD);

  switch (val) {
    case USBDEV_USBSTAT_LINK_STATE_VALUE_DISCONNECTED:
      *link_state = kDifUsbdevLinkStateDisconnected;
      break;
    case USBDEV_USBSTAT_LINK_STATE_VALUE_POWERED:
      *link_state = kDifUsbdevLinkStatePowered;
      break;
    case USBDEV_USBSTAT_LINK_STATE_VALUE_POWERED_SUSPENDED:
      *link_state = kDifUsbdevLinkStatePoweredSuspended;
      break;
    case USBDEV_USBSTAT_LINK_STATE_VALUE_ACTIVE:
      *link_state = kDifUsbdevLinkStateActive;
      break;
    case USBDEV_USBSTAT_LINK_STATE_VALUE_SUSPENDED:
      *link_state = kDifUsbdevLinkStateSuspended;
      break;
    case USBDEV_USBSTAT_LINK_STATE_VALUE_ACTIVE_NOSOF:
      *link_state = kDifUsbdevLinkStateActiveNoSof;
      break;
    case USBDEV_USBSTAT_LINK_STATE_VALUE_RESUMING:
      *link_state = kDifUsbdevLinkStateResuming;
      break;
    default:
      return kDifError;
  }

  return kDifOk;
}

dif_result_t dif_usbdev_status_get_sense(const dif_usbdev_t *usbdev,
                                         bool *sense) {
  if (usbdev == NULL || sense == NULL) {
    return kDifBadArg;
  }

  *sense = mmio_region_get_bit32(usbdev->base_addr, USBDEV_USBSTAT_REG_OFFSET,
                                 USBDEV_USBSTAT_SENSE_BIT);

  return kDifOk;
}

dif_result_t dif_usbdev_status_get_available_fifo_depth(
    const dif_usbdev_t *usbdev, uint8_t *depth) {
  if (usbdev == NULL || depth == NULL) {
    return kDifBadArg;
  }

  uint32_t reg_val =
      mmio_region_read32(usbdev->base_addr, USBDEV_USBSTAT_REG_OFFSET);
  // Note: Size of available FIFO depth is 4 bits.
  *depth =
      (uint8_t)bitfield_field32_read(reg_val, USBDEV_USBSTAT_AV_DEPTH_FIELD);

  return kDifOk;
}

dif_result_t dif_usbdev_status_get_available_fifo_full(
    const dif_usbdev_t *usbdev, bool *is_full) {
  if (usbdev == NULL || is_full == NULL) {
    return kDifBadArg;
  }

  uint32_t reg_val =
      mmio_region_read32(usbdev->base_addr, USBDEV_USBSTAT_REG_OFFSET);
  *is_full = bitfield_bit32_read(reg_val, USBDEV_USBSTAT_AV_FULL_BIT);

  return kDifOk;
}

dif_result_t dif_usbdev_status_get_rx_fifo_depth(const dif_usbdev_t *usbdev,
                                                 uint8_t *depth) {
  if (usbdev == NULL || depth == NULL) {
    return kDifBadArg;
  }

  uint32_t reg_val =
      mmio_region_read32(usbdev->base_addr, USBDEV_USBSTAT_REG_OFFSET);
  // Note: Size of RX FIFO depth is 4 bits.
  *depth =
      (uint8_t)bitfield_field32_read(reg_val, USBDEV_USBSTAT_RX_DEPTH_FIELD);

  return kDifOk;
}

dif_result_t dif_usbdev_status_get_rx_fifo_empty(const dif_usbdev_t *usbdev,
                                                 bool *is_empty) {
  if (usbdev == NULL || is_empty == NULL) {
    return kDifBadArg;
  }

  uint32_t reg_val =
      mmio_region_read32(usbdev->base_addr, USBDEV_USBSTAT_REG_OFFSET);
  *is_empty = bitfield_bit32_read(reg_val, USBDEV_USBSTAT_RX_EMPTY_BIT);

  return kDifOk;
}

dif_result_t dif_usbdev_set_osc_test_mode(const dif_usbdev_t *usbdev,
                                          dif_toggle_t enable) {
  if (usbdev == NULL || !dif_is_valid_toggle(enable)) {
    return kDifBadArg;
  }
  bool set_tx_osc_mode = dif_toggle_to_bool(enable);
  uint32_t reg_val =
      mmio_region_read32(usbdev->base_addr, USBDEV_PHY_CONFIG_REG_OFFSET);
  reg_val = bitfield_bit32_write(
      reg_val, USBDEV_PHY_CONFIG_TX_OSC_TEST_MODE_BIT, set_tx_osc_mode);
  mmio_region_write32(usbdev->base_addr, USBDEV_PHY_CONFIG_REG_OFFSET, reg_val);
  return kDifOk;
}

dif_result_t dif_usbdev_set_wake_enable(const dif_usbdev_t *usbdev,
                                        dif_toggle_t enable) {
  if (usbdev == NULL || !dif_is_valid_toggle(enable)) {
    return kDifBadArg;
  }
  uint32_t reg_val;
  if (dif_toggle_to_bool(enable)) {
    reg_val =
        bitfield_bit32_write(0, USBDEV_WAKE_CONTROL_SUSPEND_REQ_BIT, true);
  } else {
    reg_val = bitfield_bit32_write(0, USBDEV_WAKE_CONTROL_WAKE_ACK_BIT, true);
  }
  mmio_region_write32(usbdev->base_addr, USBDEV_WAKE_CONTROL_REG_OFFSET,
                      reg_val);
  return kDifOk;
}

dif_result_t dif_usbdev_get_wake_status(const dif_usbdev_t *usbdev,
                                        dif_usbdev_wake_status_t *status) {
  if (usbdev == NULL || status == NULL) {
    return kDifBadArg;
  }
  uint32_t reg_val =
      mmio_region_read32(usbdev->base_addr, USBDEV_WAKE_EVENTS_REG_OFFSET);
  status->active =
      bitfield_bit32_read(reg_val, USBDEV_WAKE_EVENTS_MODULE_ACTIVE_BIT);
  status->disconnected =
      bitfield_bit32_read(reg_val, USBDEV_WAKE_EVENTS_DISCONNECTED_BIT);
  status->bus_reset =
      bitfield_bit32_read(reg_val, USBDEV_WAKE_EVENTS_BUS_RESET_BIT);
  return kDifOk;
}

dif_result_t dif_usbdev_resume_link_to_active(const dif_usbdev_t *usbdev) {
  if (usbdev == NULL) {
    return kDifBadArg;
  }
  uint32_t reg_val =
      mmio_region_read32(usbdev->base_addr, USBDEV_USBCTRL_REG_OFFSET);
  reg_val = bitfield_bit32_write(reg_val, USBDEV_USBCTRL_RESUME_LINK_ACTIVE_BIT,
                                 true);
  mmio_region_write32(usbdev->base_addr, USBDEV_USBCTRL_REG_OFFSET, reg_val);
  return kDifOk;
}

dif_result_t dif_usbdev_get_phy_pins_status(
    const dif_usbdev_t *usbdev, dif_usbdev_phy_pins_sense_t *status) {
  if (usbdev == NULL || status == NULL) {
    return kDifBadArg;
  }
  uint32_t reg_val =
      mmio_region_read32(usbdev->base_addr, USBDEV_PHY_PINS_SENSE_REG_OFFSET);
  status->rx_dp =
      bitfield_bit32_read(reg_val, USBDEV_PHY_PINS_SENSE_RX_DP_I_BIT);
  status->rx_dn =
      bitfield_bit32_read(reg_val, USBDEV_PHY_PINS_SENSE_RX_DN_I_BIT);
  status->rx_d = bitfield_bit32_read(reg_val, USBDEV_PHY_PINS_SENSE_RX_D_I_BIT);
  status->tx_dp =
      bitfield_bit32_read(reg_val, USBDEV_PHY_PINS_SENSE_TX_DP_O_BIT);
  status->tx_dn =
      bitfield_bit32_read(reg_val, USBDEV_PHY_PINS_SENSE_TX_DN_O_BIT);
  status->tx_d = bitfield_bit32_read(reg_val, USBDEV_PHY_PINS_SENSE_TX_D_O_BIT);
  status->tx_se0 =
      bitfield_bit32_read(reg_val, USBDEV_PHY_PINS_SENSE_TX_SE0_O_BIT);
  status->output_enable =
      bitfield_bit32_read(reg_val, USBDEV_PHY_PINS_SENSE_TX_OE_O_BIT);
  status->vbus_sense =
      bitfield_bit32_read(reg_val, USBDEV_PHY_PINS_SENSE_PWR_SENSE_BIT);
  return kDifOk;
}

dif_result_t dif_usbdev_set_phy_pins_state(
    const dif_usbdev_t *usbdev, dif_toggle_t override_enable,
    dif_usbdev_phy_pins_drive_t overrides) {
  if (usbdev == NULL || !dif_is_valid_toggle(override_enable)) {
    return kDifBadArg;
  }
  bool drive_en = dif_toggle_to_bool(override_enable);
  uint32_t reg_val =
      bitfield_bit32_write(0, USBDEV_PHY_PINS_DRIVE_EN_BIT, drive_en);
  if (drive_en) {
    reg_val = bitfield_bit32_write(reg_val, USBDEV_PHY_PINS_DRIVE_DP_O_BIT,
                                   overrides.dp);
    reg_val = bitfield_bit32_write(reg_val, USBDEV_PHY_PINS_DRIVE_DN_O_BIT,
                                   overrides.dn);
    reg_val = bitfield_bit32_write(reg_val, USBDEV_PHY_PINS_DRIVE_D_O_BIT,
                                   overrides.data);
    reg_val = bitfield_bit32_write(reg_val, USBDEV_PHY_PINS_DRIVE_SE0_O_BIT,
                                   overrides.se0);
    reg_val = bitfield_bit32_write(reg_val, USBDEV_PHY_PINS_DRIVE_OE_O_BIT,
                                   overrides.output_enable);
    reg_val =
        bitfield_bit32_write(reg_val, USBDEV_PHY_PINS_DRIVE_RX_ENABLE_O_BIT,
                             overrides.diff_receiver_enable);
    reg_val =
        bitfield_bit32_write(reg_val, USBDEV_PHY_PINS_DRIVE_DP_PULLUP_EN_O_BIT,
                             overrides.dp_pullup_en);
    reg_val =
        bitfield_bit32_write(reg_val, USBDEV_PHY_PINS_DRIVE_DN_PULLUP_EN_O_BIT,
                             overrides.dn_pullup_en);
  }
  mmio_region_write32(usbdev->base_addr, USBDEV_PHY_PINS_DRIVE_REG_OFFSET,
                      reg_val);
  return kDifOk;
}
