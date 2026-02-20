// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_DIF_DIF_USBDEV_H_
#define OPENTITAN_SW_DEVICE_LIB_DIF_DIF_USBDEV_H_

/**
 * @file
 * @brief <a href="/book/hw/ip/usbdev/">USB Device</a> Device Interface
 * Functions
 */

#include <stddef.h>
#include <stdint.h>

#include "sw/device/lib/base/macros.h"
#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/dif/dif_base.h"

#include "sw/device/lib/dif/autogen/dif_usbdev_autogen.h"

#ifdef __cplusplus
extern "C" {
#endif  // __cplusplus

/**
 * Hardware constants.
 */
#define USBDEV_NUM_ENDPOINTS 12
#define USBDEV_MAX_PACKET_SIZE 64
// Internal constant that should not be used by clients. Defined here because
// it is used in the definition of `dif_usbdev_buffer_pool` below.
#define USBDEV_NUM_BUFFERS 32

// Constants used for the `dif_usbdev_endpoint_id` direction field.
#define USBDEV_ENDPOINT_DIR_IN 1
#define USBDEV_ENDPOINT_DIR_OUT 0

typedef struct dif_usbdev_endpoint_id {
  /**
   * Endpoint number.
   */
  unsigned int number : 4;
  /**
   * Reserved. Should be zero.
   */
  unsigned int reserved : 3;
  /**
   * Endpoint direction. 1 = IN endpoint, 0 = OUT endpoint
   */
  unsigned int direction : 1;
} dif_usbdev_endpoint_id_t;

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
  uint8_t buffers[USBDEV_NUM_BUFFERS];
  int8_t top;
} dif_usbdev_buffer_pool_t;

/**
 * Buffer types.
 */
typedef enum dif_usbdev_buffer_type {
  /**
   * For reading payloads of incoming packets.
   */
  kDifUsbdevBufferTypeRead,
  /**
   * For writing payloads of outgoing packets.
   */
  kDifUsbdevBufferTypeWrite,
  /**
   * Clients must not use a buffer after it is handed over to hardware or
   * returned to the free buffer pool. This type exists to protect against such
   * cases.
   */
  kDifUsbdevBufferTypeStale,
} dif_usbdev_buffer_type_t;

/**
 * A USB device buffer.
 *
 * This struct represents a USB device buffer that has been provided to a client
 * in response to a buffer request. Clients should treat instances of this
 * struct as opaque objects and should pass them to the appropriate functions of
 * this library to read and write payloads of incoming and outgoing packets,
 * respectively.
 *
 * See also: `dif_usbdev_recv`, `dif_usbdev_buffer_read`,
 * `dif_usbdev_buffer_request`, `dif_usbdev_buffer_write`,
 * `dif_usbdev_send`, `dif_usbdev_buffer_return`.
 */
typedef struct dif_usbdev_buffer {
  /**
   * Hardware buffer id.
   */
  uint8_t id;
  /**
   * Byte offset for the next read or write operation.
   */
  uint8_t offset;
  /**
   * For read buffers: remaining number of bytes to read.
   * For write buffers: remaining number of bytes that can be written.
   */
  uint8_t remaining_bytes;
  /**
   * Type of this buffer.
   */
  dif_usbdev_buffer_type_t type;
} dif_usbdev_buffer_t;

/**
 * Configuration for initializing a USB device.
 */
typedef struct dif_usbdev_config {
  /**
   * Activate the single-ended D signal for detecting K and J symbols, for use
   * with a differential receiver.
   */
  dif_toggle_t have_differential_receiver;
  /**
   * Use the TX interface with D and SE0 signals instead of Dp/Dn, for use with
   * certain transceivers.
   */
  dif_toggle_t use_tx_d_se0;
  /*
   * Recognize a single SE0 bit as end of packet instead of requiring
   * two bits.
   */
  dif_toggle_t single_bit_eop;
  /**
   * Flip the D+/D- pins.
   */
  dif_toggle_t pin_flip;
  /**
   * Reference signal generation for clock synchronization.
   */
  dif_toggle_t clock_sync_signals;
} dif_usbdev_config_t;

/**
 * Test mode of USB device. These are mutually exclusive.
 */
typedef enum dif_usbdev_test_mode {
  /**
   * Normal operation; no test mode is enabled.
   */
  kDifUsbdevTestModeNone,
  /**
   * Oscillator test mode. usbdev transmits a continuous 0101 pattern for
   * evaluating the reference clock's quality. This may also be useful for
   * electrical compliance testing. It is present in all versions.
   */
  kDifUsbdevTestModeTxOsc,
  /**
   * Packet transmission test mode. usbdev transmits a programmed IN data
   * packet continuously until a Bus Reset is received. This is NOT present
   * in Earl Grey silicon.
   */
  kDifUsbdevTestModeTxPacket,
} dif_usbdev_test_mode_t;

/**
 * Configures a USB device with runtime information.
 *
 * This function should need to be called once for the lifetime of `handle`.
 *
 * @param usbdev A USB device.
 * @param buffer_pool A USB device buffer pool.
 * @param config Runtime configuration parameters for a USB device.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_usbdev_configure(const dif_usbdev_t *usbdev,
                                  dif_usbdev_buffer_pool_t *buffer_pool,
                                  dif_usbdev_config_t config);

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
 * @param buffer_pool A USB device buffer pool.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_usbdev_fill_available_fifos(
    const dif_usbdev_t *usbdev, dif_usbdev_buffer_pool_t *buffer_pool);

/**
 * Enable or disable reception of SETUP packets for an endpoint.
 *
 * This controls whether the pair of IN and OUT endpoints with the specified
 * endpoint number are control endpoints.
 *
 * @param usbdev A USB device.
 * @param endpoint An endpoint number.
 * @param new_state New SETUP packet reception state.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_usbdev_endpoint_setup_enable(const dif_usbdev_t *usbdev,
                                              uint8_t endpoint,
                                              dif_toggle_t new_state);

/**
 * Enable or disable reception of OUT packets for an active endpoint.
 *
 * When disabling reception of OUT packets, what the endpoint will do depends
 * on other factors. If the endpoint is currently configured as a control
 * endpoint (receives SETUP packets) or it is configured as an isochronous
 * endpoint, disabling reception of OUT packets will cause them to be ignored.
 *
 * If the endpoint is neither a control nor isochronous endpoint, then its
 * behavior depends on whether it is configured to respond with STALL. If the
 * STALL response is not active, then disabling reception will cause usbdev to
 * NAK the packet. Otherwise, the STALL response takes priority, regardless of
 * the setting here.
 *
 * @param usbdev A USB device.
 * @param endpoint An OUT endpoint number.
 * @param new_state New OUT packet reception state.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_usbdev_endpoint_out_enable(const dif_usbdev_t *usbdev,
                                            uint8_t endpoint,
                                            dif_toggle_t new_state);

/**
 * Enable or disable clearing the out_enable bit after completion of an OUT
 * transaction to an endpoint.
 *
 * If set_nak_out is enabled, an OUT endpoint will disable reception of OUT
 * packets after each successful OUT transaction to that endpoint, requiring a
 * call to `dif_usbdev_endpoint_out_enable()` to enable reception again.
 *
 * @param usbdev A USB device.
 * @param endpoint An OUT endpoint number.
 * @param new_state New set_nak_on_out state.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_usbdev_endpoint_set_nak_out_enable(const dif_usbdev_t *usbdev,
                                                    uint8_t endpoint,
                                                    dif_toggle_t new_state);

/**
 * Enable or disable STALL for an endpoint.
 *
 * @param usbdev A USB device.
 * @param endpoint An endpoint ID.
 * @param new_state New STALL state.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_usbdev_endpoint_stall_enable(const dif_usbdev_t *usbdev,
                                              dif_usbdev_endpoint_id_t endpoint,
                                              dif_toggle_t new_state);

/**
 * Get STALL state of an endpoint.
 *
 * @param usbdev A USB device.
 * @param endpoint An endpoint ID.
 * @param[out] state Current STALL state.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_usbdev_endpoint_stall_get(const dif_usbdev_t *usbdev,
                                           dif_usbdev_endpoint_id_t endpoint,
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
OT_WARN_UNUSED_RESULT
dif_result_t dif_usbdev_endpoint_iso_enable(const dif_usbdev_t *usbdev,
                                            dif_usbdev_endpoint_id_t endpoint,
                                            dif_toggle_t new_state);

/**
 * Enable or disable an endpoint.
 *
 * An enabled endpoint responds to packets from the host. A disabled endpoint
 * ignores them.
 *
 * @param usbdev A USB device.
 * @param endpoint An endpoint.
 * @param new_state New endpoint state.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_usbdev_endpoint_enable(const dif_usbdev_t *usbdev,
                                        dif_usbdev_endpoint_id_t endpoint,
                                        dif_toggle_t new_state);

/**
 * Enable the USB interface of a USB device.
 *
 * Calling this function causes the USB device to assert the full-speed pull-up
 * signal to indicate its presence to the host. Ensure the default endpoint is
 * set up before enabling the interface.
 *
 * @param usbdev A USB device.
 * @param new_state New interface state.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_usbdev_interface_enable(const dif_usbdev_t *usbdev,
                                         dif_toggle_t new_state);

/**
 * Information about a received packet.
 */
typedef struct dif_usbdev_rx_packet_info {
  /**
   * Endpoint of the packet.
   */
  uint8_t endpoint;
  /**
   * Payload length in bytes.
   */
  uint8_t length;
  /**
   * Indicates if the packet is a SETUP packet.
   */
  bool is_setup;
} dif_usbdev_rx_packet_info_t;

/**
 * Get the packet at the front of RX FIFO.
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
 * - Calling this function, i.e. `dif_usbdev_recv`, and
 * - Calling `dif_usbdev_buffer_read` until the entire packet payload
 * is read.
 *
 * In order to read an incoming packet, clients should first call this function
 * to get information about the packet and the buffer that holds the packet
 * payload. Then, clients should call `dif_usbdev_buffer_read` with this buffer
 * one or more times (depending on the sizes of their internal buffers) until
 * the entire packet payload is read. Once the entire payload is read, the
 * buffer is returned to the free buffer pool. If the clients want to ignore the
 * payload of a packet, e.g. for an unsupported or a zero-length packet, they
 * can call `dif_usbdev_buffer_return` to immediately return the buffer to the
 * free buffer pool.
 *
 * @param usbdev A USB device.
 * @param[out] packet_info Packet information.
 * @param[out] buffer Buffer that holds the packet payload.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_usbdev_recv(const dif_usbdev_t *usbdev,
                             dif_usbdev_rx_packet_info_t *packet_info,
                             dif_usbdev_buffer_t *buffer);

/**
 * Read incoming packet payload.
 *
 * Clients should call this function with a buffer provided by `dif_usbdev_recv`
 * to read the payload of an incoming packet. This function copies the smaller
 * of `dst_len` and remaining number of bytes in the buffer to `dst`. The buffer
 * that holds the packet payload is returned to the free buffer pool when the
 * entire packet payload is read.
 *
 * See also: `dif_usbdev_recv`.
 *
 * @param usbdev A USB device.
 * @param buffer_pool A USB device buffer pool.
 * @param buffer A buffer provided by `dif_usbdev_recv`.
 * @param[out] dst Destination buffer.
 * @param dst_len Length of the destination buffer.
 * @param[out] bytes_written Number of bytes written to destination buffer.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_usbdev_buffer_read(const dif_usbdev_t *usbdev,
                                    dif_usbdev_buffer_pool_t *buffer_pool,
                                    dif_usbdev_buffer_t *buffer, uint8_t *dst,
                                    size_t dst_len, size_t *bytes_written);

/**
 * Return a buffer to the free buffer pool.
 *
 * This function immediately returns the given buffer to the free buffer pool.
 * Since `dif_usbdev_buffer_read` and `dif_usbdev_get_tx_status` return the
 * buffers that they work on to the free buffer pool automatically, this
 * function should only be called to discard the payload of a received
 * packet or a packet that was being prepared for transmission before it is
 * queued for transmission from an endpoint.
 *
 * See also: `dif_usbdev_recv`, `dif_usbdev_buffer_request`.
 *
 * @param usbdev A USB device.
 * @param buffer_pool A USB device buffer pool.
 * @param buffer A buffer provided by `dif_usbdev_recv` or
 *               `dif_usbdev_buffer_request`.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_usbdev_buffer_return(const dif_usbdev_t *usbdev,
                                      dif_usbdev_buffer_pool_t *buffer_pool,
                                      dif_usbdev_buffer_t *buffer);

/**
 * Request a buffer for outgoing packet payload.
 *
 * Clients should call this function to request a buffer to write the payload of
 * an outgoing packet. Sending a packet from a particular endpoint to the host
 * involves four main steps:
 * - Calling this function, i.e. `dif_usbdev_buffer_request`,
 * - Calling `dif_usbdev_buffer_write`,
 * - Calling `dif_usbdev_send`, and
 * - Calling `dif_usbdev_get_tx_status`.
 *
 * In order to send a packet, clients should first call this function to obtain
 * a buffer for the packet payload. Clients should then call
 * `dif_usbdev_buffer_write` (one or more times depending on the sizes of their
 * internal buffers) to write the packet payload to this buffer. After writing
 * the packet payload, clients should call `dif_usbdev_send` to mark the packet
 * as ready for transmission from a particular endpoint. Then, clients should
 * call `dif_usbdev_get_tx_status` to check the status of the transmission.
 * `dif_usbdev_get_tx_status` returns the buffer that holds the packet payload
 * to the free buffer pool once the packet is either successfully transmitted or
 * canceled due to an incoming SETUP packet or a link reset. If the packet
 * should no longer be sent, clients can call `dif_usbdev_buffer_return` to
 * return the buffer to the free buffer pool as long as `dif_usbdev_send` is not
 * called yet.
 *
 * See also: `dif_usbdev_buffer_write`, `dif_usbdev_send`,
 * `dif_usbdev_get_tx_status`, `dif_usbdev_buffer_return`.
 *
 * @param usbdev A USB device.
 * @param buffer_pool A USB device buffer pool.
 * @param[out] buffer A buffer for writing outgoing packet payload.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_usbdev_buffer_request(const dif_usbdev_t *usbdev,
                                       dif_usbdev_buffer_pool_t *buffer_pool,
                                       dif_usbdev_buffer_t *buffer);

/**
 * Write outgoing packet payload.
 *
 * Clients should call this function with a buffer provided by
 * `dif_usbdev_buffer_request` to write the payload of an outgoing packet. This
 * function copies the smaller of `src_len` and remaining number of bytes in the
 * buffer to the buffer. Clients should then call `dif_usbdev_send` to queue the
 * packet for transmission from a particular endpoint.
 *
 * See also: `dif_usbdev_buffer_request`, `dif_usbdev_send`,
 * `dif_usbdev_get_tx_status`, `dif_usbdev_buffer_return`.
 *
 * @param usbdev A USB device.
 * @param buffer A buffer provided by `dif_usbdev_buffer_request`.
 * @param src Source buffer.
 * @param src_len Length of the source buffer.
 * @param[out] bytes_written Number of bytes written to the USB device buffer.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_usbdev_buffer_write(const dif_usbdev_t *usbdev,
                                     dif_usbdev_buffer_t *buffer,
                                     const uint8_t *src, size_t src_len,
                                     size_t *bytes_written);

/**
 * Mark a packet ready for transmission from an endpoint.
 *
 * The USB device has 12 endpoints, each of which can be used to send packets to
 * the host. Since a packet is not actually transmitted to the host until the
 * host sends an IN token, clients must write the packet payload to a device
 * buffer and mark it as ready for transmission from a particular endpoint. A
 * packet queued for transmission from a particular endpoint is transmitted once
 * the host sends an IN token for that endpoint.
 *
 * After a packet is queued for transmission, clients should check its status by
 * calling `dif_usbdev_get_tx_status`. While the USB device handles transmission
 * errors automatically by retrying transmission, transmission of a packet may
 * be canceled if the endpoint receives a SETUP packet or the link is reset
 * before the queued packet is transmitted. In these cases, clients should
 * handle the SETUP packet or the link reset first and then optionally send the
 * same packet again. Clients must also make sure that the given endpoint does
 * not already have a packet pending for transmission before calling this
 * function.
 *
 * See also: `dif_usbdev_buffer_request`, `dif_usbdev_buffer_write`,
 * `dif_usbdev_get_tx_status`, `dif_usbdev_buffer_return`.
 *
 * @param usbdev A USB device.
 * @param endpoint An OUT endpoint number.
 * @param buffer A buffer provided by `dif_usbdev_buffer_request`.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_usbdev_send(const dif_usbdev_t *usbdev, uint8_t endpoint,
                             dif_usbdev_buffer_t *buffer);

/**
 * Get which IN endpoints have sent packets.
 *
 * This function provides which endpoints have buffers that have successfully
 * completed transmission to the host. It may be used to guide calls to
 * `dif_usbdev_clear_tx_status` to return the used buffer to the pool and clear
 * the state for the next transaction.
 *
 * @param usbdev A USB device.
 * @param[out] sent A bitmap of which endpoints have sent packets.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_usbdev_get_tx_sent(const dif_usbdev_t *usbdev, uint16_t *sent);

/**
 * Clear the TX state of the provided endpoint and restore its associated buffer
 * to the pool.
 *
 * Note that this function should only be called when an endpoint has been
 * provided a buffer. Without it, the buffer pool will become corrupted, as this
 * function does not check the status.
 *
 * In addition, if the endpoint has not yet completed or canceled the
 * transaction, the user must not call this function while the device is in an
 * active state. Otherwise, the user risks corrupting an ongoing transaction.
 *
 * @param usbdev A USB device.
 * @param buffer_pool A USB device buffer pool.
 * @param endpoint An IN endpoint number.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_usbdev_clear_tx_status(const dif_usbdev_t *usbdev,
                                        dif_usbdev_buffer_pool_t *buffer_pool,
                                        uint8_t endpoint);

/**
 * Status of an outgoing packet.
 */
typedef enum dif_usbdev_tx_status {
  /**
   *  There is no packet for the given OUT endpoint.
   */
  kDifUsbdevTxStatusNoPacket,
  /**
   * Packet is pending transmission.
   */
  kDifUsbdevTxStatusPending,
  /**
   * Packet was sent successfully.
   */
  kDifUsbdevTxStatusSent,
  /**
   * Transmission was canceled due to an incoming SETUP packet.
   */
  kDifUsbdevTxStatusCancelled,
} dif_usbdev_tx_status_t;

/**
 * Get the status of a packet that has been queued to be sent from an endpoint.
 *
 * While the USB device handles transmission errors automatically by retrying
 * transmission, transmission of a packet may be canceled if the endpoint
 * receives a SETUP packet or the link is reset before the queued packet is
 * transmitted. In these cases, clients should handle the SETUP packet or the
 * link reset first and then optionally send the same packet again.
 *
 * This function does not modify any device state. `dif_usbdev_clear_tx_status`
 * can be used to clear the status and return the buffer to the pool.
 *
 * @param usbdev A USB device.
 * @param endpoint An IN endpoint number.
 * @param[out] status Status of the packet.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_usbdev_get_tx_status(const dif_usbdev_t *usbdev,
                                      uint8_t endpoint,
                                      dif_usbdev_tx_status_t *status);

/**
 * Set the address of a USB device.
 *
 * @param usbdev A USB device.
 * @param addr New address. Only the last 7 bits are significant.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_usbdev_address_set(const dif_usbdev_t *usbdev, uint8_t addr);

/**
 * Get the address of a USB device.
 *
 * @param usbdev A USB device.
 * @param[out] addr Current address.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_usbdev_address_get(const dif_usbdev_t *usbdev, uint8_t *addr);

/**
 * Read the data toggle bits of the OUT endpoints.
 *
 * @param usbdev A USB device.
 * @param[out]toggles Current state of OUT data toggle bits.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_usbdev_data_toggle_out_read(const dif_usbdev_t *usbdev,
                                             uint16_t *toggles);

/**
 * Read the data toggle bits of the IN endpoints.
 *
 * @param usbdev A USB device.
 * @param[out]toggles Current state of IN data toggle bits.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_usbdev_data_toggle_in_read(const dif_usbdev_t *usbdev,
                                            uint16_t *toggles);

/**
 * Write to the data toggle bits of a subset of the OUT endpoints.
 * Set 1 in `mask` to change the data toggle bit of an OUT endpoint to the value
 * of the corresponding bit in `state`.
 *
 * @param usbdev A USB device.
 * @param mask Mask of OUT endpoint data toggles to be changed.
 * @param state New states of that OUT endpoint data toggles being changed.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_usbdev_data_toggle_out_write(const dif_usbdev_t *usbdev,
                                              uint16_t mask, uint16_t state);

/**
 * Write to the data toggle bits of a subset of the IN endpoints.
 * Set 1 in `mask` to change the data toggle bit of an IN endpoint to the value
 * of the corresponding bit in `state`.
 *
 * @param usbdev A USB device.
 * @param mask Mask of IN endpoint data toggles to be changed.
 * @param state New states of that IN endpoint data toggles being changed.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_usbdev_data_toggle_in_write(const dif_usbdev_t *usbdev,
                                             uint16_t mask, uint16_t state);

/**
 * Clear the data toggle bits for the selected endpoint.
 *
 * @param usbdev A USB device.
 * @param endpoint An endpoint number.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_usbdev_clear_data_toggle(const dif_usbdev_t *usbdev,
                                          uint8_t endpoint);

/**
 * Get USB frame index.
 *
 * @param usbdev A USB device.
 * @param[out] frame_index USB frame index.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_usbdev_status_get_frame(const dif_usbdev_t *usbdev,
                                         uint16_t *frame_index);

/**
 * Check if the host is lost.
 *
 * The host is lost if the link is still active but a start of frame packet has
 * not been received in the last 4.096ms.
 *
 * @param usbdev A USB device.
 * @param[out] host_lost Status of the host. `true` if the host is lost, `false`
 * otherwise.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_usbdev_status_get_host_lost(const dif_usbdev_t *usbdev,
                                             bool *host_lost);

/**
 * USB link state.
 */
typedef enum dif_usbdev_link_state {
  kDifUsbdevLinkStateDisconnected,
  kDifUsbdevLinkStatePowered,
  kDifUsbdevLinkStatePoweredSuspended,
  kDifUsbdevLinkStateActive,
  kDifUsbdevLinkStateSuspended,
  kDifUsbdevLinkStateActiveNoSof,
  kDifUsbdevLinkStateResuming,
} dif_usbdev_link_state_t;

/**
 * Get USB link state.
 *
 * @param usbdev A USB device.
 * @param[out] link_state USB link state.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_usbdev_status_get_link_state(
    const dif_usbdev_t *usbdev, dif_usbdev_link_state_t *link_state);

/**
 * Get the state of the sense pin.
 *
 * @param usbdev A USB device.
 * @param[out] sense State of the sense pin. `true` if the host is providing
 * VBUS, `false` otherwise.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_usbdev_status_get_sense(const dif_usbdev_t *usbdev,
                                         bool *sense);

/**
 * Get the depths of the AV OUT and AV SETUP FIFOs.
 *
 * See also: `dif_usbdev_fill_available_fifos`.
 *
 * @param usbdev A USB device.
 * @param[out] setup_depth Depth of the AV SETUP FIFO.
 * @param[out] out_depth Depth of the AV OUT FIFO.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_usbdev_status_get_available_fifo_depths(
    const dif_usbdev_t *usbdev, uint8_t *setup_depth, uint8_t *out_depth);
/**
 * Check if AV OUT and AV SETUP FIFOs are full.
 *
 * See also: `dif_usbdev_fill_available_fifos`.
 *
 * @param usbdev A USB device.
 * @param[out] setup_is_full State of the AV SETUP FIFO. `true` if full, false
 * otherwise.
 * @param[out] out_is_full State of the AV OUT FIFO. `true` if full, false
 * otherwise.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_usbdev_status_get_available_fifo_full(
    const dif_usbdev_t *usbdev, bool *setup_is_full, bool *out_is_full);
/**
 * Get the depth of the RX FIFO.
 *
 * See also: `dif_usbdev_recv`.
 *
 * @param usbdev A USB device.
 * @param[out] depth Depth of the RX FIFO.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_usbdev_status_get_rx_fifo_depth(const dif_usbdev_t *usbdev,
                                                 uint8_t *depth);

/**
 * Check if the RX FIFO is empty.
 *
 * See also: `dif_usbdev_recv`.
 *
 * @param usbdev A USB device.
 * @param[out] is_empty State of the RX FIFO. `true` if empty, `false`
 * otherwise.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_usbdev_status_get_rx_fifo_empty(const dif_usbdev_t *usbdev,
                                                 bool *is_empty);

/**
 * Enable a test mode, or disable all test modes.
 *
 * @param usbdev A USB device.
 * @param mode The test mode should be enabled, if any.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_usbdev_set_test_mode(const dif_usbdev_t *usbdev,
                                      dif_usbdev_test_mode_t mode);

/**
 * Control whether the AON wake module is active.
 *
 * @param usbdev A USB device.
 * @param enable Whether the AON wake module is enabled.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_usbdev_set_wake_enable(const dif_usbdev_t *usbdev,
                                        dif_toggle_t enable);

typedef struct dif_usbdev_wake_status {
  /** Whether the AON wake module is active. */
  bool active;
  /** Whether the USB disconnected while the AON wake module was active. */
  bool disconnected;
  /** Whether the USB was reset while the AON wake module was active. */
  bool bus_reset;
  /** Whether the USB became non-Idle whilst the AON wake module was active. */
  bool bus_not_idle;
} dif_usbdev_wake_status_t;

/**
 * Get the status of the AON wake module.
 *
 * Note that the conditions triggering exit from suspended state must be read
 * before disabling the AON wake module. Once the AON wake module is
 * deactivated, that status information is lost.
 *
 * Also note that the ordinary resume condition does not report to the usbdev
 * module. Instead, it should be obtained from the module monitoring wakeup
 * sources.
 *
 * @param usbdev A USB device.
 * @param[out] status The status of the module.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_usbdev_get_wake_status(const dif_usbdev_t *usbdev,
                                        dif_usbdev_wake_status_t *status);

/**
 * Force the link state machine to resume to an active state.
 *
 * This is used when waking from a low-power suspended state to resume to an
 * active state. It moves the usbdev out of the Powered state (from the USB
 * device state machine in the spec) without receiving a bus reset. Without help
 * from software, the usbdev module cannot determine on its own when a bus reset
 * is required.
 *
 * @param usbdev A USB device.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_usbdev_resume_link_to_active(const dif_usbdev_t *usbdev);

typedef struct dif_usbdev_phy_pins_sense {
  /** USB D+ input. */
  bool rx_dp : 1;
  /** USB D- input. */
  bool rx_dn : 1;
  /** USB data input from an external differential receiver, if available. */
  bool rx_d : 1;
  /** USB transmit D+ output. */
  bool tx_dp : 1;
  /** USB transmit D- output. */
  bool tx_dn : 1;
  /** USB transmit data value output. */
  bool tx_d : 1;
  /** USB single-ended zero output. */
  bool tx_se0 : 1;
  /** USB output enable for D+ / D-. */
  bool output_enable : 1;
  /** USB VBUS sense pin. */
  bool vbus_sense : 1;
} dif_usbdev_phy_pins_sense_t;

/**
 * Get the current state of the USB PHY pins.
 *
 * @param usbdev A USB device.
 * @param[out] status The current state of the pins.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_usbdev_get_phy_pins_status(
    const dif_usbdev_t *usbdev, dif_usbdev_phy_pins_sense_t *status);

typedef struct dif_usbdev_phy_pins_drive {
  /** USB D+ output, for use with dn. */
  bool dp : 1;
  /** USB D- output. for use with dp. */
  bool dn : 1;
  /** USB data output, encoding K and J when se0 is 0. */
  bool data : 1;
  /** USB single-ended zero output. */
  bool se0 : 1;
  /** USB output enable for D+ / D-. */
  bool output_enable : 1;
  /** Enable control pin for the differential receiver. */
  bool diff_receiver_enable : 1;
  /** Controls whether to pull up the D+ pin. */
  bool dp_pullup_en : 1;
  /** Controls whether to pull up the D- pin. */
  bool dn_pullup_en : 1;
} dif_usbdev_phy_pins_drive_t;

/**
 * Control whether to override the USB PHY and drive pins as GPIOs.
 *
 * @param usbdev A USB device.
 * @param override_enable Enable / disable the GPIO-like overrides.
 * @param overrides The values to set the pins to.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_usbdev_set_phy_pins_state(
    const dif_usbdev_t *usbdev, dif_toggle_t override_enable,
    dif_usbdev_phy_pins_drive_t overrides);

/**
 * Raw data transfer directly to the packet buffer memory. This is a faster
 * implementation of the generic `mmio_memcpy_to_mmio32` that is specialized for
 * the USB device and gives a significant performance improvement.
 *
 * @param usbdev A USB device.
 * @param id Buffer number.
 * @param src Source data.
 * @param src_len Number of bytes to transfer.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_usbdev_buffer_raw_write(const dif_usbdev_t *usbdev, uint8_t id,
                                         const uint8_t *src, size_t src_len);

/**
 * Raw data transfer directly from the packet buffer memory. This is a faster
 * implementation of the generic `mmio_memcpy_from_mmio32` that is specialized
 * for the USB device and gives a significant performance improvemenet.
 *
 * @param usbdev A USB device.
 * @param id Buffer number.
 * @param dst Destination buffer.
 * @param dst_len Number of bytes to transfer.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_usbdev_buffer_raw_read(const dif_usbdev_t *usbdev, uint8_t id,
                                        uint8_t *dst, size_t dst_len);

#ifdef __cplusplus
}  // extern "C"
#endif  // __cplusplus

#endif  // OPENTITAN_SW_DEVICE_LIB_DIF_DIF_USBDEV_H_
