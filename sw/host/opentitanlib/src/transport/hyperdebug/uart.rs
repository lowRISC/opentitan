// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use std::cell::RefCell;
use std::rc::Rc;
use std::time::Duration;

use anyhow::Result;
use rusb::{Direction, Recipient, RequestType};
use serialport::Parity;

use super::UartInterface;
use crate::io::nonblocking_help::NonblockingHelp;
use crate::io::uart::Uart;
use crate::transport::common::uart::SerialPortUart;
use crate::transport::TransportError;
use crate::util::usb::UsbBackend;

const UART_BAUD: u32 = 115200;

pub struct HyperdebugUart {
    usb_device: Rc<RefCell<UsbBackend>>,
    usb_interface: u8,
    supports_clearing_queues: bool,
    serial_port: SerialPortUart,
}

#[allow(dead_code)]
enum ControlRequest {
    ReqParity = 0,
    SetParity = 1,
    ReqBaud = 2,
    SetBaud = 3,
    Break = 4,
    ClearQueues = 5,
}

/// Request clearing the queue of UART data having been received by HyperDebug.
#[allow(dead_code)]
const CLEAR_RX_FIFO: u16 = 0x0001;
/// Request clearing the queue of data to be transmitted by HyperDebug UART.
#[allow(dead_code)]
const CLEAR_TX_FIFO: u16 = 0x0002;

impl HyperdebugUart {
    pub fn open(
        usb_device: &Rc<RefCell<UsbBackend>>,
        uart_interface: &UartInterface,
        supports_clearing_queues: bool,
    ) -> Result<Self> {
        Ok(Self {
            usb_device: usb_device.clone(),
            usb_interface: uart_interface.interface,
            supports_clearing_queues,
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
        let usb_handle = self.usb_device.borrow();
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
        let usb_handle = self.usb_device.borrow();
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
        if self.supports_clearing_queues {
            let usb_handle = self.usb_device.borrow();
            usb_handle.write_control(
                rusb::request_type(Direction::Out, RequestType::Vendor, Recipient::Interface),
                ControlRequest::ClearQueues as u8,
                CLEAR_RX_FIFO,
                self.usb_interface as u16,
                &[],
            )?;
        }
        self.serial_port.clear_rx_buffer()
    }

    fn set_break(&self, enable: bool) -> Result<()> {
        let usb_handle = self.usb_device.borrow();
        usb_handle.write_control(
            rusb::request_type(Direction::Out, RequestType::Vendor, Recipient::Interface),
            ControlRequest::Break as u8,
            if enable { 0xFFFF } else { 0 },
            self.usb_interface as u16,
            &[],
        )?;
        Ok(())
    }

    fn set_parity(&self, parity: Parity) -> Result<()> {
        let parity_code = match parity {
            Parity::None => 0,
            Parity::Odd => 1,
            Parity::Even => 2,
        };

        let usb_handle = self.usb_device.borrow();
        usb_handle.write_control(
            rusb::request_type(Direction::Out, RequestType::Vendor, Recipient::Interface),
            ControlRequest::SetParity as u8,
            parity_code,
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
