// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use super::UartInterface;
use crate::io::nonblocking_help::NonblockingHelp;
use crate::io::uart::Uart;
use crate::transport::common::uart::SerialPortUart;
use crate::transport::hyperdebug::Inner;
use crate::transport::TransportError;
use anyhow::Result;
use rusb::{Direction, Recipient, RequestType};
use std::rc::Rc;
use std::time::Duration;

const UART_BAUD: u32 = 115200;

pub struct HyperdebugUart {
    inner: Rc<Inner>,
    usb_interface: u8,
    serial_port: SerialPortUart,
}

#[allow(dead_code)]
enum ControlRequest {
    ReqParity = 0,
    SetParity = 1,
    ReqBaud = 2,
    SetBaud = 3,
    Break = 4,
}

impl HyperdebugUart {
    pub fn open(inner: &Rc<Inner>, uart_interface: &UartInterface) -> Result<Self> {
        Ok(Self {
            inner: Rc::clone(inner),
            usb_interface: uart_interface.interface,
            serial_port: SerialPortUart::open(
                uart_interface
                    .tty
                    .to_str()
                    .ok_or(TransportError::UnicodePathError)?,
                UART_BAUD,
            )?,
        })
    }
}

impl Uart for HyperdebugUart {
    fn get_baudrate(&self) -> Result<u32> {
        let usb_handle = self.inner.usb_device.borrow();
        let mut data = [0u8, 0u8];
        usb_handle.read_control(
            rusb::request_type(Direction::In, RequestType::Vendor, Recipient::Interface),
            ControlRequest::ReqBaud as u8,
            0,
            self.usb_interface as u16,
            &mut data,
        )?;
        Ok(u16::from_le_bytes(data) as u32 * 100)
    }

    fn set_baudrate(&self, baudrate: u32) -> Result<()> {
        let usb_handle = self.inner.usb_device.borrow();
        usb_handle.write_control(
            rusb::request_type(Direction::Out, RequestType::Vendor, Recipient::Interface),
            ControlRequest::SetBaud as u8,
            ((baudrate + 50) / 100).try_into()?,
            self.usb_interface as u16,
            &[],
        )?;
        Ok(())
    }

    fn set_flow_control(&self, flow_control: bool) -> Result<()> {
        self.serial_port.set_flow_control(flow_control)
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
        let usb_handle = self.inner.usb_device.borrow();
        usb_handle.write_control(
            rusb::request_type(Direction::Out, RequestType::Vendor, Recipient::Interface),
            ControlRequest::Break as u8,
            if enable { 0xFFFF } else { 0 },
            self.usb_interface as u16,
            &[],
        )?;
        Ok(())
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
}
