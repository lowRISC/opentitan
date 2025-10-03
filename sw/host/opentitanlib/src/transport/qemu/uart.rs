// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use std::cell::RefCell;
use std::os::fd::BorrowedFd;
use std::rc::Rc;
use std::time::Duration;

use anyhow::Result;
use serialport::Parity;

use crate::io::uart::Uart;
use crate::transport::NonblockingHelp;
use crate::transport::common::uart::SerialPortUart;
use crate::transport::qemu::monitor::Monitor;

pub struct QemuUart {
    /// Connection to the QEMU monitor which can control the emulator.
    pub monitor: Rc<RefCell<Monitor>>,

    // The UART CharDev's id
    id: String,

    // Underlying SerialPort used for the UART.
    serial_port: SerialPortUart,

    // Whether the UART is currently transmitting a break condition or not.
    in_break: RefCell<bool>,
}

impl QemuUart {
    pub fn new(monitor: Rc<RefCell<Monitor>>, id: &str, serial_port: SerialPortUart) -> Self {
        Self {
            monitor,
            id: id.into(),
            serial_port,
            in_break: RefCell::new(false),
        }
    }
}

impl Uart for QemuUart {
    fn get_baudrate(&self) -> Result<u32> {
        self.serial_port.get_baudrate()
    }

    fn set_baudrate(&self, baudrate: u32) -> Result<()> {
        self.serial_port.set_baudrate(baudrate)
    }

    fn set_flow_control(&self, flow_control: bool) -> Result<()> {
        self.serial_port.set_flow_control(flow_control)
    }

    fn get_device_path(&self) -> Result<String> {
        self.serial_port.get_device_path()
    }

    fn read(&self, buf: &mut [u8]) -> Result<usize> {
        self.serial_port.read(buf)
    }

    fn read_timeout(&self, buf: &mut [u8], timeout: Duration) -> Result<usize> {
        self.serial_port.read_timeout(buf, timeout)
    }

    fn write(&self, buf: &[u8]) -> Result<()> {
        self.serial_port.write(buf)
    }

    fn clear_rx_buffer(&self) -> Result<()> {
        self.serial_port.clear_rx_buffer()
    }

    fn set_break(&self, enable: bool) -> Result<()> {
        // Assumes we have ot-uart.toggle-break=true, so always send break
        if *self.in_break.borrow() ^ enable {
            self.monitor.borrow_mut().send_chardev_break(&self.id)?;
            *self.in_break.borrow_mut() = enable;
        }
        Ok(())
    }

    fn set_parity(&self, parity: Parity) -> Result<()> {
        self.serial_port.set_parity(parity)
    }

    fn supports_nonblocking_read(&self) -> Result<bool> {
        self.serial_port.supports_nonblocking_read()
    }

    fn register_nonblocking_read(&self, registry: &mio::Registry, token: mio::Token) -> Result<()> {
        self.serial_port.register_nonblocking_read(registry, token)
    }

    fn nonblocking_help(&self) -> Result<Rc<dyn NonblockingHelp>> {
        self.serial_port.nonblocking_help()
    }

    fn borrow_fd(&self) -> Result<BorrowedFd> {
        self.serial_port.borrow_fd()
    }
}

impl Drop for QemuUart {
    fn drop(&mut self) {
        // Stop transmitting break before deleting the UART
        if *self.in_break.borrow() {
            let _ = self.monitor.borrow_mut().send_chardev_break(&self.id);
            *self.in_break.borrow_mut() = false;
        }
    }
}
