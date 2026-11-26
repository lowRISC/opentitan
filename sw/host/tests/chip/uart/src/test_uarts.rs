// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

//! Host UARTs of the UART tests.
//!
//! Each OT UART can only reach a few pads, so each one is wired to its own host UART.

use std::rc::Rc;

use anyhow::Result;

use opentitanlib::app::TransportWrapper;
use opentitanlib::io::uart::Uart;
use opentitanlib::test_utils::mem::MemWriteReq;

/// Returns the host UART wired to the pads of OT uart `uart_idx`.
pub fn ot_uart(transport: &TransportWrapper, uart_idx: u8) -> Result<Rc<dyn Uart>> {
    transport.uart(&format!("ot_uart{uart_idx}"))
}

/// Tells the device which UART to test and returns the console and the UART under test.
///
/// Call it once the device waits for commands. When testing uart0, the device moves its console
/// to uart2. Old output on uart2 is dropped before the device starts printing there.
///
/// The host transmitter of ot_uart2 is armed by the optional UART2_HOST_TX strapping while uart2
/// is in use and released again for the other UARTs.
pub fn select_uart(
    transport: &TransportWrapper,
    boot_console: &dyn Uart,
    uart_idx_addr: u32,
    uart_idx: u8,
) -> Result<(Rc<dyn Uart>, Rc<dyn Uart>)> {
    if let Some(strapping) = transport.optional_pin_strapping("UART2_HOST_TX")? {
        if uart_idx == 0 || uart_idx == 2 {
            strapping.apply()?;
        } else {
            strapping.remove()?;
        }
    }
    let console = if uart_idx == 0 {
        ot_uart(transport, 2)?
    } else {
        transport.uart("console")?
    };
    let uart = ot_uart(transport, uart_idx)?;
    boot_console.set_flow_control(true)?;
    if uart_idx == 0 {
        console.clear_rx_buffer()?;
        console.set_flow_control(true)?;
    }
    MemWriteReq::execute(boot_console, uart_idx_addr, &[uart_idx])?;
    uart.set_flow_control(false)?;
    Ok((console, uart))
}
