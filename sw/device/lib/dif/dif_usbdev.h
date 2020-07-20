// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_DIF_DIF_USBDEV_H_
#define OPENTITAN_SW_DEVICE_LIB_DIF_DIF_USBDEV_H_

#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/dif/dif_warn_unused_result.h"
#include <stddef.h>
#include <stdint.h>

/**
 * Hardware constants.
 */
#define USBDEV_NUM_ENDPOINTS 12
#define USBDEV_MAX_PACKET_SIZE 64
// Internal constant that should not be used by clients. Defined here because
// it is used in the definition of `dif_usbdev_buffer_pool` below.
#define USBDEV_NUM_BUFFERS 32

/**
 * Free buffer pool.
 *
 * A USB device has a fixed number of buffers that are used for storing incoming
 * and outgoing packets and the software is responsible for keeping track of
 * free buffers. The pool is implemented as a stack for constant-time add and
 * remove. `top` points to the last free buffer added to the pool. The pool is
 * full when `top == USBDEV_NUM_BUFFERS - 1` and empty when `top == -1`.
 */
typedef struct dif_usbdev_buffer_pool {
  uint8_t entries[USBDEV_NUM_BUFFERS];
  int8_t top;
} dif_usbdev_buffer_pool_t;

/**
 * State of a read buffer operation.
 *
 * This struct is used to track the state of a read buffer operation internally.
 * Thus, clients can freely choose their buffer sizes and easily process
 * packets that are larger than their buffers by simply calling
 * `dif_usbdev_rx_packet_read_bytes` repeatedly until they read the entire
 * payload of each packet.
 *
 * See also: `dif_usbdev_rx_packet_get_info`, `dif_usbdev_rx_packet_read_bytes`.
 */
typedef struct dif_usbdev_read_buffer_op_state {
  /**
   * Buffer to read from.
   */
  uint8_t buffer_entry;
  /**
   * Number of remaining bytes.
   */
  size_t remaining_bytes;
  /**
   * Offset to start reading from.
   */
  size_t offset;
} dif_usbdev_read_buffer_op_state_t;

/**
 * Internal state of a USB device.
 *
 * Instances of this struct must be initialized by `dif_usbdev_init()` before
 * being passed to other functions in this library. Its fields should be
 * considered private and are only provided here so that callers can allocate
 * it.
 */
typedef struct dif_usbdev {
  mmio_region_t base_addr;
  dif_usbdev_buffer_pool_t buffer_pool;
  dif_usbdev_read_buffer_op_state_t read_buffer_op_state;
  uint16_t active_buffer_ops;
} dif_usbdev_t;

/**
 * Enumeration for enabling/disabling various functionality.
 */
typedef enum dif_usbdev_toggle {
  kDifUsbdevToggleDisable,
  kDifUsbdevToggleEnable,
} dif_usbdev_toggle_t;

/**
 * Set of allowed configurations for USB power sense override.
 */
typedef enum dif_usbdev_power_sense_override {
  kDifUsbdevPowerSenseOverrideDisabled,
  kDifUsbdevPowerSenseOverridePresent,
  kDifUsbdevPowerSenseOverrideNotPresent
} dif_usbdev_power_sense_override_t;

/**
 * Configuration for initializing a USB device.
 */
typedef struct dif_usbdev_config {
  /**
   * Base address of the USB device.
   */
  mmio_region_t base_addr;
  /**
   * Use the differential rx signal instead of the single-ended signals.
   */
  dif_usbdev_toggle_t differential_rx;
  /**
   * Use the differential tx signal instead of the single-ended signals.
   */
  dif_usbdev_toggle_t differential_tx;
  /*
   * Recognize a single SE0 bit as end of packet instead of requiring
   * two bits.
   */
  dif_usbdev_toggle_t single_bit_eop;
  /**
   * Override USB power sense.
   */
  dif_usbdev_power_sense_override_t power_sense_override;
} dif_usbdev_config_t;

/**
 * Common return codes for the functions in this library.
 */
typedef enum dif_usbdev_result {
  /**
   * Indicates that the call succeeded.
   */
  kDifUsbdevOK = 0,
  /**
   * Indicates that a non-specific error occurred and the hardware is in an
   * invalid or irrecoverable state.
   */
  kDifUsbdevError = 1,
  /**
   * Indicates that the caller supplied invalid arguments but the call did not
   * cause any side-effects and the hardware is in a valid and recoverable
   * state.
   */
  kDifUsbdevBadArg = 2,
} dif_usbdev_result_t;

/**
 * Initialize a USB device.
 *
 * A USB device must first be initialized by this function before calling other
 * functions in this library.
 *
 * @param config Configuration for initializing a USB device.
 * @param usbdev Internal state of the initialized USB device.
 * @return The result of the operation.
 */
DIF_WARN_UNUSED_RESULT
dif_usbdev_result_t dif_usbdev_init(dif_usbdev_config_t *config,
                                    dif_usbdev_t *usbdev);

/**
 * Fill the available buffer FIFO of a USB device.
 *
 * The USB device has a small FIFO (AV FIFO) that stores free buffers for
 * incoming packets. It is the responsibility of the software to ensure that the
 * AV FIFO is never empty. If the host tries to send a packet when the AV FIFO
 * is empty, the USB device will respond with a NAK. While this will typically
 * cause the host to retry transmission for regular data packets, there are
 * transactions in the USB protocol during which the USB device is not allowed
 * to send a NAK. Thus, the software must make sure that the AV FIFO is never
 * empty by calling this function periodically.
 *
 * @param usbdev A USB device.
 * @return The result of the operation.
 */
DIF_WARN_UNUSED_RESULT
dif_usbdev_result_t dif_usbdev_fill_available_fifo(dif_usbdev_t *usbdev);

/**
 * Enable or disable reception of SETUP packets for an endpoint.
 *
 * @param usbdev A USB device.
 * @param endpoint An endpoint.
 * @param new_state New SETUP packet reception state.
 * @return The result of the operation.
 */
DIF_WARN_UNUSED_RESULT
dif_usbdev_result_t dif_usbdev_endpoint_setup_enable(
    dif_usbdev_t *usbdev, uint8_t endpoint, dif_usbdev_toggle_t new_state);

/**
 * Enable or disable reception of OUT packets for an endpoint.
 *
 * @param usbdev A USB device.
 * @param endpoint An endpoint.
 * @param new_state New OUT packet reception state.
 * @return The result of the operation.
 */
DIF_WARN_UNUSED_RESULT
dif_usbdev_result_t dif_usbdev_endpoint_out_enable(
    dif_usbdev_t *usbdev, uint8_t endpoint, dif_usbdev_toggle_t new_state);

/**
 * Enable or disable STALL for an endpoint.
 *
 * @param usbdev A USB device.
 * @param endpoint An endpoint.
 * @param new_state New STALL state.
 * @return The result of the operation.
 */
DIF_WARN_UNUSED_RESULT
dif_usbdev_result_t dif_usbdev_endpoint_stall_enable(
    dif_usbdev_t *usbdev, uint8_t endpoint, dif_usbdev_toggle_t new_state);

/**
 * Get STALL state of an endpoint.
 *
 * @param usbdev A USB device.
 * @param endpoint An endpoint.
 * @param state Current STALL state.
 * @return The result of the operation.
 */
DIF_WARN_UNUSED_RESULT
dif_usbdev_result_t dif_usbdev_endpoint_stall_get(dif_usbdev_t *usbdev,
                                                  uint8_t endpoint,
                                                  bool *state);

/**
 * Enable or disable isochronous mode for an endpoint.
 *
 * Isochronous endpoints transfer data periodically. Since isochronous transfers
 * do not have a handshaking stage, isochronous endpoints cannot report errors
 * or STALL conditions.
 *
 * @param usbdev A USB device.
 * @param endpoint An endpoint.
 * @param new_state New isochronous state.
 * @return The result of the operation.
 */
DIF_WARN_UNUSED_RESULT
dif_usbdev_result_t dif_usbdev_endpoint_iso_enable(
    dif_usbdev_t *usbdev, uint8_t endpoint, dif_usbdev_toggle_t new_state);

/**
 * Enable the USB interface of a USB device.
 *
 * Calling this function causes the USB device to assert the full-speed pull-up
 * signal to indicate its presence to the host.
 *
 * @param usbdev A USB device.
 * @param new_state New interface state.
 * @return The result of the operation.
 */
DIF_WARN_UNUSED_RESULT
dif_usbdev_result_t dif_usbdev_interface_enable(dif_usbdev_t *usbdev,
                                                dif_usbdev_toggle_t new_state);

/**
 * Information about a received packet.
 */
typedef struct dif_usbdev_rx_packet_info {
  /**
   * Endpoint of the packet.
   */
  uint8_t endpoint;
  /**
   * Length of the packet in bytes.
   */
  uint8_t len;
  /**
   * Indicates if the packet is a SETUP packet.
   */
  bool is_setup;
} dif_usbdev_rx_packet_info_t;

/**
 * Return codes for `dif_usbdev_rx_packet_get_info`.
 */
typedef enum dif_usbdev_rx_packet_get_info_result {
  /**
   * Indicates that the call succeeded.
   */
  kDifUsbdevRxPacketGetInfoResultOK = kDifUsbdevOK,
  /**
   * Indicates that a non-specific error occurred and the hardware is in an
   * invalid or irrecoverable state.
   */
  kDifUsbdevRxPacketGetInfoResultError = kDifUsbdevError,
  /**
   * Indicates that the caller supplied invalid arguments but the call did not
   * cause any side-effects and the hardware is in a valid and recoverable
   * state.
   */
  kDifUsbdevRxPacketGetInfoResultBadArg = kDifUsbdevBadArg,
  /**
   * Indicates that there is already a read buffer operation in progress.
   */
  kDifUsbdevRxPacketGetInfoResultBusy,
  /**
   * Indicates that RX FIFO is empty.
   */
  kDifUsbdevRxPacketGetInfoResultNoPackets,
} dif_usbdev_rx_packet_get_info_result_t;

/**
 * Get information about the packet at the front of RX FIFO.
 *
 * The USB device has a small FIFO (RX FIFO) that stores received packets until
 * the software has a chance to process them. It is the responsibility of the
 * software to ensure that the RX FIFO is never full. If the host tries to send
 * a packet when the RX FIFO is full, the USB device will respond with a NAK.
 * While this will typically cause the host to retry transmission for regular
 * data packets, there are transactions in the USB protocol during which the USB
 * device is not allowed to send a NAK. Thus, the software must read received
 * packets as soon as possible.
 *
 * Reading received packets involves two main steps:
 * - Calling this function, i.e. `dif_usbdev_rx_packet_get_info`, and
 * - Calling `dif_usbdev_rx_packet_read_bytes` until the entire packet payload
 * is read or calling `dif_usbdev_rx_packet_discard_bytes`.
 *
 * In order to read an incoming packet, clients should first call this function
 * to get information about the packet. In addition to populating a
 * `dif_usbdev_rx_packet_info_t` struct, this also starts an internal read
 * buffer operation. The state of this operation, i.e. the buffer to read from,
 * number of bytes remaining and the offset to start reading from, is tracked by
 * this library, therefore clients do not need to perform any additional state
 * tracking. Then, clients should call `dif_usbdev_rx_packet_read_bytes` one or
 * more times (depending on the sizes of their internal buffers) until the
 * entire packet payload is read. Once the entire packet is read, the read
 * buffer operation ends and the buffer that holds the packet payload is
 * returned to the free buffer pool. If the clients want to ignore the payload
 * of a packet, e.g. for an unsupported or a zero-length packet, they can call
 * `dif_usbdev_rx_packet_discard_bytes` to immediately return the buffer that
 * holds the packet payload to the free buffer pool and end the read buffer
 * operation.
 *
 * @param usbdev A USB device.
 * @return The result of the operation.
 */
DIF_WARN_UNUSED_RESULT
dif_usbdev_rx_packet_get_info_result_t dif_usbdev_rx_packet_get_info(
    dif_usbdev_t *usbdev, dif_usbdev_rx_packet_info_t *packet);

/**
 * Return codes for `dif_usbdev_rx_packet_read_bytes`.
 */
typedef enum dif_usbdev_rx_packet_read_bytes_result {
  /**
   * Indicates that the call succeeded and the entire packet payload is read.
   */
  kDifUsbdevRxPacketReadBytesResultOK = kDifUsbdevOK,
  /**
   * Indicates that a non-specific error occurred and the hardware is in an
   * invalid or irrecoverable state.
   */
  kDifUsbdevRxPacketReadBytesResultError = kDifUsbdevError,
  /**
   * Indicates that the caller supplied invalid arguments but the call did not
   * cause any side-effects and the hardware is in a valid and recoverable
   * state.
   */
  kDifUsbdevRxPacketReadBytesResultBadArg = kDifUsbdevBadArg,
  /**
   * Indicates that the call was successful but there are remaining bytes to be
   * read.
   */
  kDifUsbdevRxPacketReadBytesResultContinue,
  /**
   * Indicates that there is no active read buffer operation.
   */
  kDifUsbdevRxPacketReadBytesResultNotReading,
} dif_usbdev_rx_packet_read_bytes_result_t;

/**
 * Read the payload of the last received packet.
 *
 * The clients should call this function to read the payload of the last
 * received packet after calling `dif_usbdev_rx_packet_get_info`. This function
 * copies the smaller of `dst_len` and remaining number of bytes to `dst`. The
 * active read buffer operation ends and the buffer that holds the packet
 * payload is returned to the free buffer pool when the entire packet payload is
 * read.
 *
 * See also: `dif_usbdev_rx_packet_get_info`.
 *
 * @param usbdev A USB device.
 * @return The result of the operation.
 */
DIF_WARN_UNUSED_RESULT
dif_usbdev_rx_packet_read_bytes_result_t dif_usbdev_rx_packet_read_bytes(
    dif_usbdev_t *usbdev, uint8_t *dst, size_t dst_len, size_t *bytes_written);

/**
 * Return codes for `dif_usbdev_rx_packet_discard_bytes`.
 */
typedef enum dif_usbdev_rx_packet_discard_bytes_result {
  /**
   * Indicates that the call succeeded.
   */
  kDifUsbdevRxPacketDiscardBytesResultOK = kDifUsbdevOK,
  /**
   * Indicates that a non-specific error occurred and the hardware is in an
   * invalid or irrecoverable state.
   */
  kDifUsbdevRxPacketDiscardBytesResultError = kDifUsbdevError,
  /**
   * Indicates that the caller supplied invalid arguments but the call did not
   * cause any side-effects and the hardware is in a valid and recoverable
   * state.
   */
  kDifUsbdevRxPacketDiscardBytesResultBadArg = kDifUsbdevBadArg,
  /**
   * Indicates that there is no active read buffer operation.
   */
  kDifUsbdevRxPacketDiscardBytesResultNotReading,
} dif_usbdev_rx_packet_discard_bytes_result_t;

/**
 * Discard the payload of the last received packet.
 *
 * The clients should call this function to discard the payload of the last
 * received packet after calling `dif_usbdev_rx_packet_get_info`. This function
 * immediately ends the active read buffer operation and returns the buffer
 * that holds the packet payload to the free buffer pool.
 *
 * See also: `dif_usbdev_rx_packet_get_info`.
 *
 * @param usbdev A USB device.
 * @return The result of the operation.
 */
DIF_WARN_UNUSED_RESULT
dif_usbdev_rx_packet_discard_bytes_result_t dif_usbdev_rx_packet_discard_bytes(
    dif_usbdev_t *usbdev);

/**
 * Return codes for `dif_usbdev_tx_packet_write_bytes`.
 */
typedef enum dif_usbdev_tx_packet_write_bytes_result {
  /**
   * Indicates that the call succeeded.
   */
  kDifUsbdevTxPacketWriteBytesResultOK = kDifUsbdevOK,
  /**
   * Indicates that a non-specific error occurred and the hardware is in an
   * invalid or irrecoverable state.
   */
  kDifUsbdevTxPacketWriteBytesResultError = kDifUsbdevError,
  /**
   * Indicates that the caller supplied invalid arguments but the call did not
   * cause any side-effects and the hardware is in a valid and recoverable
   * state.
   */
  kDifUsbdevTxPacketWriteBytesResultBadArg = kDifUsbdevBadArg,
  /**
   * Indicates that there are no free buffers.
   */
  kDifUsbdevTxPacketWriteBytesResultNoBuffers,
  /**
   * Indicates that the requested write exceeds the device buffer size.
   */
  kDifUsbdevTxPacketWriteBytesResultBufferFull,
  /**
   * Indicates that the endpoint already has a packet pending transmission.
   */
  kDifUsbdevTxPacketWriteBytesResultBusy,
} dif_usbdev_tx_packet_write_bytes_result_t;

/**
 * Write outgoing packet payload for an endpoint.
 *
 * The USB device has 12 endpoints, each of which can be used to send packets to
 * the host. Since a packet is not actually transmitted to the host until the
 * host sends an IN token, clients must write the packet payload to a device
 * buffer and mark it as ready for transmission from a particular endpoint. Note
 * that this can be done in parallel for multiple endpoints. A packet queued for
 * transmission from a particular endpoint is transmitted once the host sends an
 * IN token for that endpoint.
 *
 * After a packet is queued for transmission, clients should periodically check
 * its status. While the USB device handles transmission errors automatically by
 * retrying transmission, transmission of a packet may be canceled if the
 * endpoint receives a SETUP packet or the link is reset before the queued
 * packet is transmitted. In these cases, clients should handle the SETUP packet
 * or the link reset first and then optionally send the same packet again.
 *
 * Sending a packet from a particular endpoint to the host involves three main
 * steps:
 * - Calling this function, i.e. `dif_usbdev_tx_packet_write_bytes`,
 * - Calling `dif_usbdev_tx_packet_send`, and
 * - Calling `dif_usbdev_tx_packet_get_status`.
 *
 * In order to send a packet, clients should first call this function (one or
 * more times depending on the sizes of their internal buffers) to write the
 * packet payload to a device buffer. Calling this function also starts an
 * internal write buffer operation similar to `dif_usbdev_rx_packet_get_info`.
 * After writing the packet payload, clients should call
 * `dif_usbdev_tx_packet_send` to mark the packet as ready for transmission,
 * which also ends the active write buffer operation. Then, clients should
 * periodically call `dif_usbdev_tx_packet_get_status` to check the status of
 * the packet. `dif_usbdev_tx_packet_get_status` returns the buffer that holds
 * the packet payload to the free buffer pool once the packet is either
 * successfully transmitted or canceled due to an incoming SETUP packet.
 *
 * @param usbdev A USB device.
 * @param endpoint An endpoint.
 * @param src Source buffer.
 * @param src_len Length of the source buffer.
 * @bytes_written Number of bytes written to the USB device buffer.
 * @return The result of the operation.
 */
DIF_WARN_UNUSED_RESULT
dif_usbdev_tx_packet_write_bytes_result_t dif_usbdev_tx_packet_write_bytes(
    dif_usbdev_t *usbdev, uint8_t endpoint, uint8_t *src, size_t src_len,
    size_t *bytes_written);

/**
 * Return codes for `dif_usbdev_tx_packet_send`.
 */
typedef enum dif_usbdev_tx_packet_send_result {
  /**
   * Indicates that the call succeeded.
   */
  kDifUsbdevTxPacketSendResultOK = kDifUsbdevOK,
  /**
   * Indicates that a non-specific error occurred and the hardware is in an
   * invalid or irrecoverable state.
   */
  kDifUsbdevTxPacketSendResultError = kDifUsbdevError,
  /**
   * Indicates that the caller supplied invalid arguments but the call did not
   * cause any side-effects and the hardware is in a valid and recoverable
   * state.
   */
  kDifUsbdevTxPacketSendResultBadArg = kDifUsbdevBadArg,
  /**
   * Indicates that the endpoint does not have a packet to be sent.
   */
  kDifUsbdevTxPacketSendResultNotWriting,
} dif_usbdev_tx_packet_send_result_t;

/**
 * Mark the packet buffered for the given endpoint as ready for transmission.
 *
 * See also: `dif_usbdev_tx_packet_write_bytes`.
 *
 * @param usbdev A USB device.
 * @param endpoint An endpoint.
 * @return The result of the operation.
 */
DIF_WARN_UNUSED_RESULT
dif_usbdev_tx_packet_send_result_t dif_usbdev_tx_packet_send(
    dif_usbdev_t *usbdev, uint8_t endpoint);

/**
 * Status of an outgoing packet.
 */
typedef enum dif_usbdev_tx_packet_status {
  /**
   *  There is no packet for the given endpoint.
   */
  kDifUsbdevTxPacketStatusNoPacket,
  /**
   * There is an active write buffer operation and the packet is not marked as
   * ready for transmission yet.
   */
  kDifUsbdevTxPacketStatusStillWriting,
  /**
   * Packet is pending transmission.
   */
  kDifUsbdevTxPacketStatusPending,
  /**
   * Packet was sent successfully.
   */
  kDifUsbdevTxPacketStatusSent,
  /**
   * Transmission was canceled due to an incoming SETUP packet.
   */
  kDifUsbdevTxPacketStatusCancelled,
} dif_usbdev_tx_packet_status_t;

/**
 * Get the status of a packet that has been queued to be sent from an endpoint.
 *
 * @param usbdev A USB device.
 * @param endpoint An endpoint.
 * @param status Status of the packet.
 * @return The result of the operation.
 */
DIF_WARN_UNUSED_RESULT
dif_usbdev_result_t dif_usbdev_tx_packet_get_status(
    dif_usbdev_t *usbdev, uint8_t endpoint,
    dif_usbdev_tx_packet_status_t *status);

/**
 * Set the address of a USB device.
 *
 * @param usbdev A USB device.
 * @param addr New address. Only the last 7 bits are significant.
 * @return The result of the operation.
 */
DIF_WARN_UNUSED_RESULT
dif_usbdev_result_t dif_usbdev_address_set(dif_usbdev_t *usbdev, uint8_t addr);

/**
 * Get the address of a USB device.
 *
 * @param usbdev A USB device.
 * @param addr Current address.
 * @return The result of the operation.
 */
DIF_WARN_UNUSED_RESULT
dif_usbdev_result_t dif_usbdev_address_get(dif_usbdev_t *usbdev, uint8_t *addr);

/**
 * Get USB frame index.
 *
 * @param usbdev A USB device.
 * @param frame_index USB frame index.
 * @return The result of the operation.
 */
DIF_WARN_UNUSED_RESULT
dif_usbdev_result_t dif_usbdev_status_get_frame(dif_usbdev_t *usbdev,
                                                uint16_t *frame_index);

/**
 * Check if the host is lost.
 *
 * The host is lost if the link is still active but a start of frame packet has
 * not been received in the last 4.096ms.
 *
 * @param usbdev A USB device.
 * @param host_lost Status of the host. `true` if the host is lost, `false`
 * otherwise.
 * @return The result of the operation.
 */
DIF_WARN_UNUSED_RESULT
dif_usbdev_result_t dif_usbdev_status_get_host_lost(dif_usbdev_t *usbdev,
                                                    bool *host_lost);

/**
 * USB link state.
 */
typedef enum dif_usbdev_link_state {
  kDifUsbdevLinkStateDisconnected,
  kDifUsbdevLinkStatePowered,
  kDifUsbdevLinkStatePoweredSuspend,
  kDifUsbdevLinkStateActive,
  kDifUsbdevLinkStateSuspend,
} dif_usbdev_link_state_t;

/**
 * Get USB link state.
 *
 * @param usbdev A USB device.
 * @param link_state USB link state.
 * @return The result of the operation.
 */
DIF_WARN_UNUSED_RESULT
dif_usbdev_result_t dif_usbdev_status_get_link_state(
    dif_usbdev_t *usbdev, dif_usbdev_link_state_t *link_state);

/**
 * Get the state of the sense pin.
 *
 * @param usbdev A USB device.
 * @param sense State of the sense pin. `true` if the host is providing VBUS,
 * `false` otherwise.
 * @return The result of the operation.
 */
DIF_WARN_UNUSED_RESULT
dif_usbdev_result_t dif_usbdev_status_get_sense(dif_usbdev_t *usbdev,
                                                bool *sense);

/**
 * Get the depth of the AV FIFO.
 *
 * See also: `dif_usbdev_fill_available_fifo`.
 *
 * @param usbdev A USB device.
 * @param depth Depth of the AV FIFO.
 * @return The result of the operation.
 */
DIF_WARN_UNUSED_RESULT
dif_usbdev_result_t dif_usbdev_status_get_available_fifo_depth(
    dif_usbdev_t *usbdev, uint8_t *depth);
/**
 * Check if AV FIFO is full.
 *
 * See also: `dif_usbdev_fill_available_fifo`.
 *
 * @param usbdev A USB device.
 * @param is_full State of the AV FIFO. `true` if full, false otherwise.
 * @return The result of the operation.
 */
DIF_WARN_UNUSED_RESULT
dif_usbdev_result_t dif_usbdev_status_get_available_fifo_full(
    dif_usbdev_t *usbdev, bool *is_full);
/**
 * Get the depth of the RX FIFO.
 *
 * See also: `dif_usbdev_rx_packet_get_info`.
 *
 * @param usbdev A USB device.
 * @param depth Depth of the RX FIFO.
 * @return The result of the operation.
 */
DIF_WARN_UNUSED_RESULT
dif_usbdev_result_t dif_usbdev_status_get_rx_fifo_depth(dif_usbdev_t *usbdev,
                                                        uint8_t *depth);

/**
 * Check if the RX FIFO is empty.
 *
 * See also: `dif_usbdev_rx_packet_get_info`.
 *
 * @param usbdev A USB device.
 * @param is_empty State of the RX FIFO. `true` if empty, `false` otherwise.
 * @return The result of the operation.
 */
DIF_WARN_UNUSED_RESULT
dif_usbdev_result_t dif_usbdev_status_get_rx_fifo_empty(dif_usbdev_t *usbdev,
                                                        bool *is_empty);

/**
 * USB device interrupts.
 */
typedef enum dif_usbdev_irq {
  /**
   * \internal First USB device interrupt.
   */
  kDifUsbdevIrqFirst,
  /**
   * A packet was received as part of an OUT or SETUP transaction.
   */
  kDifUsbdevIrqPktReceived = kDifUsbdevIrqFirst,
  /**
   * A packet was sent as part of an IN transaction.
   */
  kDifUsbdevIrqPktSent,
  /**
   * VBUS was lost and the link was disconnected.
   */
  kDifUsbdevIrqDisconnected,
  /**
   * A Start-of-Frame (SOF) packet was not received on an active link
   * for 4.096 ms. The host must send a SOF packet every 1 ms.
   */
  kDifUsbdevIrqHostLost,
  /**
   * Link was reset by the host.
   */
  kDifUsbdevIrqLinkReset,
  /**
   * Link was suspended by the host.
   */
  kDifUsbdevIrqLinkSuspend,
  /**
   * Link became active again after being suspended.
   */
  kDifUsbdevIrqLinkResume,
  /**
   * Available buffer FIFO was empty.
   */
  kDifUsbdevIrqAvEmpty,
  /**
   * Received buffer FIFO was full.
   */
  kDifUsbdevIrqRxFull,
  /**
   * A write was done to available buffer FIFO when it was full.
   */
  kDifUsbdevIrqAvOverflow,
  /**
   * The ACK packet expected in response to an IN transaction was
   * not received.
   */
  kDifUsbdevIrqLinkInError,
  /**
   * A CRC error occurred.
   */
  kDifUsbdevIrqRxCrcError,
  /**
   * A packet with an invalid packet identifier (PID) was received.
   */
  kDifUsbdevIrqRxPidError,
  /**
   * A packet with invalid bitstuffing was received.
   */
  kDifUsbdevIrqRxBitstuffError,
  /**
   * USB frame number was updated with a valid SOF packet.
   */
  kDifUsbdevIrqFrame,
  /**
   * VBUS was detected.
   */
  kDifUsbdevIrqConnected,
  /**
   * \internal Last USB device interrupt.
   */
  kDifUsbdevIrqLast = kDifUsbdevIrqConnected
} dif_usbdev_irq_t;

/**
 * Enable or disable an interrupt.
 *
 * @param usbdev A USB device.
 * @param irq An interrupt.
 * @param state New state of the interrupt.
 * @return The result of the operation.
 */
DIF_WARN_UNUSED_RESULT
dif_usbdev_result_t dif_usbdev_irq_enable(dif_usbdev_t *usbdev,
                                          dif_usbdev_irq_t irq,
                                          dif_usbdev_toggle_t state);

/**
 * Check if there is a pending request for an interrupt.
 *
 * @param usbdev A USB device.
 * @param irq An interrupt.
 * @param state State of the interrupt.
 * @return The result of the operation.
 */
DIF_WARN_UNUSED_RESULT
dif_usbdev_result_t dif_usbdev_irq_get(dif_usbdev_t *usbdev,
                                       dif_usbdev_irq_t irq, bool *state);

/**
 * Clear an interrupt.
 *
 * @param usbdev A USB device.
 * @param irq An interrupt.
 * @return The result of the operation.
 */
DIF_WARN_UNUSED_RESULT
dif_usbdev_result_t dif_usbdev_irq_clear(dif_usbdev_t *usbdev,
                                         dif_usbdev_irq_t irq);

/**
 * Clear all pending interrupts.
 *
 * @param usbdev A USB device.
 * @return The result of the operation.
 */
DIF_WARN_UNUSED_RESULT
dif_usbdev_result_t dif_usbdev_irq_clear_all(dif_usbdev_t *usbdev);

/**
 * Disable all interrupts and optionally return the current interrupt
 * configuration.
 *
 * @param usbdev A USB device.
 * @param cur_config Current interrupt configuration.
 * @return The result of the operation.
 */
DIF_WARN_UNUSED_RESULT
dif_usbdev_result_t dif_usbdev_irq_disable_all(dif_usbdev_t *usbdev,
                                               uint32_t *cur_config);

/**
 * Restore interrupt configuration.
 *
 * @param usbdev A USB device.
 * @param new_config New interrupt configuration.
 * @return The result of the operation.
 */
DIF_WARN_UNUSED_RESULT
dif_usbdev_result_t dif_usbdev_irq_restore(dif_usbdev_t *usbdev,
                                           uint32_t new_config);

/**
 * Test an interrupt.
 *
 * @param usbdev A USB device.
 * @param irq An interrupt.
 * @return The result of the operation.
 */
DIF_WARN_UNUSED_RESULT
dif_usbdev_result_t dif_usbdev_irq_test(dif_usbdev_t *usbdev,
                                        dif_usbdev_irq_t irq);

#endif  // OPENTITAN_SW_DEVICE_LIB_DIF_DIF_USBDEV_H_
