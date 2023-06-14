// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[repr(u32)]
pub enum UartReg {
    IntrState = bindgen::dif::UART_INTR_STATE_REG_OFFSET,
    IntrEnable = bindgen::dif::UART_INTR_ENABLE_REG_OFFSET,
    IntrTest = bindgen::dif::UART_INTR_TEST_REG_OFFSET,
    AlertTest = bindgen::dif::UART_ALERT_TEST_REG_OFFSET,
    Ctrl = bindgen::dif::UART_CTRL_REG_OFFSET,
    Status = bindgen::dif::UART_STATUS_REG_OFFSET,
    Rdata = bindgen::dif::UART_RDATA_REG_OFFSET,
    Wdata = bindgen::dif::UART_WDATA_REG_OFFSET,
    FifoCtrl = bindgen::dif::UART_FIFO_CTRL_REG_OFFSET,
    FifoStatus = bindgen::dif::UART_FIFO_STATUS_REG_OFFSET,
    Ovrd = bindgen::dif::UART_OVRD_REG_OFFSET,
    Val = bindgen::dif::UART_VAL_REG_OFFSET,
    TimeoutCtrl = bindgen::dif::UART_TIMEOUT_CTRL_REG_OFFSET,
}
