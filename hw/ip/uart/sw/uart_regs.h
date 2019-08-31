// Generated register defines for uart

// Copyright information found in source file:
// Copyright lowRISC contributors.

// Licensing information found in source file:
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef _UART_REG_DEFS_
#define _UART_REG_DEFS_

// Interrupt State Register
#define UART_INTR_STATE(id) (UART##id##_BASE_ADDR + 0x0)
#define UART_INTR_STATE_TX_WATERMARK 0
#define UART_INTR_STATE_RX_WATERMARK 1
#define UART_INTR_STATE_TX_OVERFLOW 2
#define UART_INTR_STATE_RX_OVERFLOW 3
#define UART_INTR_STATE_RX_FRAME_ERR 4
#define UART_INTR_STATE_RX_BREAK_ERR 5
#define UART_INTR_STATE_RX_TIMEOUT 6
#define UART_INTR_STATE_RX_PARITY_ERR 7

// Interrupt Enable Register
#define UART_INTR_ENABLE(id) (UART##id##_BASE_ADDR + 0x4)
#define UART_INTR_ENABLE_TX_WATERMARK 0
#define UART_INTR_ENABLE_RX_WATERMARK 1
#define UART_INTR_ENABLE_TX_OVERFLOW 2
#define UART_INTR_ENABLE_RX_OVERFLOW 3
#define UART_INTR_ENABLE_RX_FRAME_ERR 4
#define UART_INTR_ENABLE_RX_BREAK_ERR 5
#define UART_INTR_ENABLE_RX_TIMEOUT 6
#define UART_INTR_ENABLE_RX_PARITY_ERR 7

// Interrupt Test Register
#define UART_INTR_TEST(id) (UART##id##_BASE_ADDR + 0x8)
#define UART_INTR_TEST_TX_WATERMARK 0
#define UART_INTR_TEST_RX_WATERMARK 1
#define UART_INTR_TEST_TX_OVERFLOW 2
#define UART_INTR_TEST_RX_OVERFLOW 3
#define UART_INTR_TEST_RX_FRAME_ERR 4
#define UART_INTR_TEST_RX_BREAK_ERR 5
#define UART_INTR_TEST_RX_TIMEOUT 6
#define UART_INTR_TEST_RX_PARITY_ERR 7

// UART control register
#define UART_CTRL(id) (UART##id##_BASE_ADDR + 0xc)
#define UART_CTRL_TX 0
#define UART_CTRL_RX 1
#define UART_CTRL_NF 2
#define UART_CTRL_SLPBK 4
#define UART_CTRL_LLPBK 5
#define UART_CTRL_PARITY_EN 6
#define UART_CTRL_PARITY_ODD 7
#define UART_CTRL_RXBLVL_MASK 0x3
#define UART_CTRL_RXBLVL_OFFSET 8
#define UART_CTRL_RXBLVL_BREAK2 0
#define UART_CTRL_RXBLVL_BREAK4 1
#define UART_CTRL_RXBLVL_BREAK8 2
#define UART_CTRL_RXBLVL_BREAK16 3
#define UART_CTRL_NCO_MASK 0xffff
#define UART_CTRL_NCO_OFFSET 16

// UART live status register
#define UART_STATUS(id) (UART##id##_BASE_ADDR + 0x10)
#define UART_STATUS_TXFULL 0
#define UART_STATUS_RXFULL 1
#define UART_STATUS_TXEMPTY 2
#define UART_STATUS_TXIDLE 3
#define UART_STATUS_RXIDLE 4
#define UART_STATUS_RXEMPTY 5

// UART read data
#define UART_RDATA(id) (UART##id##_BASE_ADDR + 0x14)
#define UART_RDATA_MASK 0xff
#define UART_RDATA_OFFSET 0

// UART write data
#define UART_WDATA(id) (UART##id##_BASE_ADDR + 0x18)
#define UART_WDATA_MASK 0xff
#define UART_WDATA_OFFSET 0

// UART FIFO control register
#define UART_FIFO_CTRL(id) (UART##id##_BASE_ADDR + 0x1c)
#define UART_FIFO_CTRL_RXRST 0
#define UART_FIFO_CTRL_TXRST 1
#define UART_FIFO_CTRL_RXILVL_MASK 0x7
#define UART_FIFO_CTRL_RXILVL_OFFSET 2
#define UART_FIFO_CTRL_RXILVL_RXLVL1 0
#define UART_FIFO_CTRL_RXILVL_RXLVL4 1
#define UART_FIFO_CTRL_RXILVL_RXLVL8 2
#define UART_FIFO_CTRL_RXILVL_RXLVL16 3
#define UART_FIFO_CTRL_RXILVL_RXLVL30 4
#define UART_FIFO_CTRL_TXILVL_MASK 0x3
#define UART_FIFO_CTRL_TXILVL_OFFSET 5
#define UART_FIFO_CTRL_TXILVL_TXLVL1 0
#define UART_FIFO_CTRL_TXILVL_TXLVL4 1
#define UART_FIFO_CTRL_TXILVL_TXLVL8 2
#define UART_FIFO_CTRL_TXILVL_TXLVL16 3

// UART FIFO status register
#define UART_FIFO_STATUS(id) (UART##id##_BASE_ADDR + 0x20)
#define UART_FIFO_STATUS_TXLVL_MASK 0x3f
#define UART_FIFO_STATUS_TXLVL_OFFSET 0
#define UART_FIFO_STATUS_RXLVL_MASK 0x3f
#define UART_FIFO_STATUS_RXLVL_OFFSET 16

// UART override control register
#define UART_OVRD(id) (UART##id##_BASE_ADDR + 0x24)
#define UART_OVRD_TXEN 0
#define UART_OVRD_TXVAL 1

// UART oversampled values
#define UART_VAL(id) (UART##id##_BASE_ADDR + 0x28)
#define UART_VAL_RX_MASK 0xffff
#define UART_VAL_RX_OFFSET 0

// UART RX timeout control
#define UART_TIMEOUT_CTRL(id) (UART##id##_BASE_ADDR + 0x2c)
#define UART_TIMEOUT_CTRL_VAL_MASK 0xffffff
#define UART_TIMEOUT_CTRL_VAL_OFFSET 0
#define UART_TIMEOUT_CTRL_EN 31

#endif  // _UART_REG_DEFS_
// End generated register defines for uart
