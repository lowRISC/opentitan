// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef _SW_DEVICE_LIB_DIF_UART_H_
#define _SW_DEVICE_LIB_DIF_UART_H_

#include <stdbool.h>
#include <stdint.h>

#include "sw/device/lib/base/mmio.h"

/**
 * UART interrupt configuration
 *
 * Enumeration used to enable, disable, test and query the UART interrupts.
 * Please see the comportability specification for more information:
 * https://docs.opentitan.org/doc/rm/comportability_specification/
 */
typedef enum dif_uart_interrupt {
  kDifUartInterruptTxWatermark = 0, /**< TX FIFO dipped below watermark */
  kDifUartInterruptRxWatermark,     /**< RX FIFO reached high watermark */
  kDifUartInterruptTxEmpty,         /**< TX FIFO empty */
  kDifUartInterruptRxOverflow,      /**< RX FIFO overflow */
  kDifUartInterruptRxFrameErr,      /**< RX framing error */
  kDifUartInterruptRxBreakErr,      /**< RX break condition */
  kDifUartInterruptRxTimeout, /**< RX FIFO timeout (not empty in a set time) */
  kDifUartInterruptRxParityErr, /**< RX parity error detection */
} dif_uart_interrupt_t;

/**
 * TX and RX FIFO depth configuration
 *
 * Enumeration used to set the upper limit of bytes to queue.
 */
typedef enum dif_uart_watermark {
  kDifUartWatermarkByte1 = 0, /**< 1 byte */
  kDifUartWatermarkByte4,     /**< 4 bytes */
  kDifUartWatermarkByte8,     /**< 8 bytes */
  kDifUartWatermarkByte16,    /**< 16 bytes */
  kDifUartWatermarkByte30,    /**< 30 bytes */
} dif_uart_watermark_t;

/**
 * Generic enable/disable enumeration
 *
 * Enumeration used to enable/disable bits, flags, ...
 */
typedef enum dif_uart_enable {
  kDifUartEnable = 0, /**< enable */
  kDifUartDisable,    /**< disable */
} dif_uart_enable_t;

/**
 * UART parity enumeration
 *
 * Enumeration used to convey parity information
 */
typedef enum dif_uart_parity {
  kDifUartParityOdd = 0, /**< odd */
  kDifUartParityEven,    /**< even */
} dif_uart_parity_t;

/**
 * UART configuration data
 *
 * The fundamental data used to configure an UART instance
 */
typedef struct dif_uart_config {
  uint32_t baudrate;               /**< Requested baudrate */
  uint32_t clk_freq_hz;            /**< Input clock frequency */
  dif_uart_enable_t parity_enable; /**< Enable parity check */
  dif_uart_parity_t parity;        /**< Set parity (even by default) */
} dif_uart_config_t;

/**
 * UART instance state
 *
 * UART persistent data that is required by all UART API. |base_address| must
 * be initialised by the caller, before passing into the UART DIF init routine.
 */
typedef struct dif_uart {
  mmio_region_t base_addr; /**< UART base address */
} dif_uart_t;

/**
 * Initialise an instance of UART
 *
 * Initialise UART instance using the configuration data in @p arg2.
 * Information that must be retained, and is required to program UART must be
 * stored in @p arg3.
 * @param base_addr Base address of an instance of UART IP block
 * @param config UART configuration data
 * @param uart UART state data
 * @return true if the function was successful, false otherwise
 */
bool dif_uart_init(mmio_region_t base_addr, const dif_uart_config_t *config,
                   dif_uart_t *uart);

/**
 * Configure an instance of UART
 *
 * Configure UART using the configuration data in @p arg2. This operation
 * performs fundamental configuration.
 *
 * @param uart UART state data
 * @param config UART configuration data
 * @return true if the function was successful, false otherwise
 */
bool dif_uart_configure(const dif_uart_t *uart,
                        const dif_uart_config_t *config);

/**
 * Set the RX FIFO watermark
 *
 * Set the RX FIFO watermark, is only useful when the corresponding interrupt
 * is enabled. When the queued RX FIFO number of bytes rises to or above this
 * level, the RX watermark interrupt is raised.
 *
 * @param uart UART state data
 * @param watermark RX FIFO watermark
 * @return true if the function was successful, false otherwise
 */
bool dif_uart_watermark_rx_set(const dif_uart_t *uart,
                               dif_uart_watermark_t watermark);
/**
 * Set the TX FIFO watermark
 *
 * Set the TX FIFO watermark, is only useful when the corresponding interrupt
 * is enabled. When the queued TX FIFO number of bytes falls to or below this
 * level, the TX watermark interrupt is raised.
 *
 * @param uart UART state data
 * @param watermark TX FIFO watermark
 * @return true if the function was successful, false otherwise
 */
bool dif_uart_watermark_tx_set(const dif_uart_t *uart,
                               dif_uart_watermark_t watermark);

/**
 * UART send bytes
 *
 * Non-blocking UART send bytes routine. Can be used from inside an UART ISR.
 * This function attempts to write @p arg3 number of bytes to the UART TX FIFO
 * from @p arg3, and passes @p arg4 back to the caller.
 *
 * @param uart UART state data
 * @param data Data to be written
 * @param bytes_requested Number of bytes requested to be written by the caller
 * @param bytes_written Number of bytes written (optional)
 * @return true if the function was successful, false otherwise
 */
bool dif_uart_bytes_send(const dif_uart_t *uart, const uint8_t *data,
                         size_t bytes_requested, size_t *bytes_written);

/**
 * UART receive bytes
 *
 * Non-blocking UART receive bytes routine. Can be used from inside an UART ISR.
 * This function attempts to read @p arg2 number of bytes from the UART RX FIFO
 * into @p arg3, and passes @p arg4 back to the caller.
 *
 * @param uart UART state data
 * @param bytes_requested Number of bytes requested to be read by the caller
 * @param data Data to be read
 * @param bytes_read Number of bytes read (optional)
 * @return true if the function was successful, false otherwise
 */
bool dif_uart_bytes_receive(const dif_uart_t *uart, size_t bytes_requested,
                            uint8_t *data, size_t *bytes_read);

/**
 * Transmit a single UART byte (polled)
 *
 * Transmit a single UART byte @p arg2. This operation is polled, and will busy
 * wait until a byte has been sent. Must not be used inside an ISR.
 *
 * @param uart UART state data
 * @param byte Byte to be transmitted
 * @return true if the function was successful, false otherwise
 */
bool dif_uart_byte_send_polled(const dif_uart_t *uart, uint8_t byte);

/**
 * Receive a single UART byte (polled)
 *
 * Receive a single UART byte and store it in @p arg2. This operation is polled,
 * and will busy wait until a byte has been read. Must not be used inside an
 * ISR.
 *
 * @param uart UART state data
 * @param byte Received byte
 * @return true if the function was successful, false otherwise
 */
bool dif_uart_byte_receive_polled(const dif_uart_t *uart, uint8_t *byte);

/**
 * UART get requested IRQ state
 *
 * Get the state of the requested IRQ in @p arg2.
 *
 * @para uart UART state data
 * @param irq_type IRQ to get the state of
 * @param state IRQ state passed back to the caller
 * @return true if the function was successful, false otherwise
 */
bool dif_uart_irq_state_get(const dif_uart_t *uart,
                            dif_uart_interrupt_t irq_type,
                            dif_uart_enable_t *state);

/**
 * UART disable interrupts
 *
 * Disable generation of all UART interrupts, and pass previous interrupt state
 * in @p arg3 back to the caller. Parameter @p arg2 is ignored if NULL.
 *
 * @param uart UART state data
 * @param state IRQ state passed back to the caller
 * @return true if the function was successful, false otherwise
 */
bool dif_uart_irqs_disable(const dif_uart_t *uart, uint32_t *state);

/**
 * UART restore IRQ state
 *
 * Restore previous UART IRQ state. This function is used to restore the
 * UART interrupt state prior to dif_uart_irqs_disable function call.
 *
 * @param uart UART state data
 * @param state IRQ state to restore
 * @return true if the function was successful, false otherwise
 */
bool dif_uart_irqs_restore(const dif_uart_t *uart, uint32_t state);

/**
 * UART interrupt control
 *
 * Enable/disable an UART interrupt specified in @p arg3.
 *
 * @param uart UART state data
 * @param irq_type UART interrupt type
 * @param enable enable or disable the interrupt
 * @return true if the function was successful, false otherwise
 */
bool dif_uart_irq_enable(const dif_uart_t *uart, dif_uart_interrupt_t irq_type,
                         dif_uart_enable_t enable);

/**
 * UART interrupt force
 *
 * Force interrupt specified in @p arg2.
 *
 * @param uart UART state data
 * @param irq_type UART interrupt type to be forced
 * @return true if the function was successful, false otherwise
 */
bool dif_uart_irq_force(const dif_uart_t *uart, dif_uart_interrupt_t irq_type);

/**
 * UART RX bytes available
 *
 * Get the number of bytes available to be read from the UART RX FIFO. This
 * function can be used to check FIFO full and empty conditions.
 *
 * @param uart UART state data
 * @param num_bytes Number of bytes available to be read
 * @return true if the function was successful, false otherwise
 */
bool dif_uart_rx_bytes_available(const dif_uart_t *uart, size_t *num_bytes);

/**
 * UART TX bytes available
 *
 * Get the number of bytes available to be written to the UART TX FIFO. This
 * function can be used to check FIFO full and empty conditions.
 *
 * @param uart UART state data
 * @param num_bytes Number of bytes available to be written
 * @return true if the function was successful, false otherwise
 */
bool dif_uart_tx_bytes_available(const dif_uart_t *uart, size_t *num_bytes);

#endif
