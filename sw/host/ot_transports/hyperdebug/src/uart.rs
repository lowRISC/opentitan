// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use std::os::fd::BorrowedFd;
use std::rc::Rc;

use anyhow::{Context, Result};
use rusb::{Direction, Recipient, RequestType};
use serialport::Parity;

use opentitanlib::io::console::ConsoleDevice;
use opentitanlib::io::uart::flow::SoftwareFlowControl;
use opentitanlib::io::uart::serial::SerialPortUart;
use opentitanlib::io::uart::{FlowControl, Uart, UartError};
use opentitanlib::transport::TransportError;

use super::{Inner, UartInterface};

const UART_BAUD: u32 = 115200;

pub struct HyperdebugUart {
    inner: Rc<Inner>,
    usb_interface: u8,
    supports_clearing_queues: bool,
    serial_port: SoftwareFlowControl<SerialPortUart>,
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
        inner: &Rc<Inner>,
        uart_interface: &UartInterface,
        supports_clearing_queues: bool,
    ) -> Result<Self> {
        Ok(Self {
            inner: inner.clone(),
            usb_interface: uart_interface.interface,
            supports_clearing_queues,
            serial_port: SoftwareFlowControl::new(SerialPortUart::open(
                uart_interface
                    .tty
                    .to_str()
                    .ok_or(TransportError::UnicodePathError)?,
                UART_BAUD,
            )?),
        })
    }
}

impl ConsoleDevice for HyperdebugUart {
    fn poll_read(
        &self,
        cx: &mut std::task::Context<'_>,
        buf: &mut [u8],
    ) -> std::task::Poll<Result<usize>> {
        self.serial_port.poll_read(cx, buf)
    }

    fn write(&self, buf: &[u8]) -> Result<()> {
        self.serial_port.write(buf)
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
        let compressed_baudrate: u16 = ((baudrate + 50) / 100).try_into()?;
        let decompressed_baudrate = compressed_baudrate as u32 * 100;
        if decompressed_baudrate != baudrate {
            log::warn!(
                "Warning: accuracy loss when setting baud rate. UART will use {} Bd instead of {}",
                decompressed_baudrate,
                baudrate
            );
        }
        usb_handle.write_control(
            rusb::request_type(Direction::Out, RequestType::Vendor, Recipient::Interface),
            ControlRequest::SetBaud as u8,
            compressed_baudrate,
            self.usb_interface as u16,
            &[],
        )?;
        Ok(())
    }

    fn get_flow_control(&self) -> Result<FlowControl> {
        self.serial_port.get_flow_control()
    }

    fn set_flow_control(&self, flow_control: bool) -> Result<()> {
        self.serial_port.set_flow_control(flow_control)
    }

    fn get_device_path(&self) -> Result<String> {
        self.serial_port.get_device_path()
    }

    fn clear_rx_buffer(&self) -> Result<()> {
        if self.supports_clearing_queues {
            let usb_handle = self.inner.usb_device.borrow();
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

    fn set_parity(&self, parity: Parity) -> Result<()> {
        // Parity values taken from https://chromium.googlesource.com/chromiumos/platform/ec/+/refs/heads/main/chip/stm32/usart.c#196
        let parity_code = match parity {
            Parity::None => 0,
            Parity::Odd => 1,
            Parity::Even => 2,
        };

        let usb_handle = self.inner.usb_device.borrow();
        usb_handle.write_control(
            rusb::request_type(Direction::Out, RequestType::Vendor, Recipient::Interface),
            ControlRequest::SetParity as u8,
            parity_code,
            self.usb_interface as u16,
            &[],
        )?;
        Ok(())
    }

    fn get_parity(&self) -> Result<Parity> {
        let usb_handle = self.inner.usb_device.borrow();
        let mut data = [0u8, 0u8];
        usb_handle.read_control(
            rusb::request_type(Direction::In, RequestType::Vendor, Recipient::Interface),
            ControlRequest::ReqParity as u8,
            0,
            self.usb_interface as u16,
            &mut data,
        )?;
        // Parity values taken from https://chromium.googlesource.com/chromiumos/platform/ec/+/refs/heads/main/chip/stm32/usart.c#180
        match u16::from_le_bytes(data) {
            0 => Ok(Parity::None),
            1 => Ok(Parity::Odd),
            2 => Ok(Parity::Even),
            _ => Err(UartError::ReadError("Unknown parity value".to_string()).into()),
        }
    }

    fn set_break(&self, enable: bool) -> Result<()> {
        let usb_handle = self.inner.usb_device.borrow();
        usb_handle
            .write_control(
                rusb::request_type(Direction::Out, RequestType::Vendor, Recipient::Interface),
                ControlRequest::Break as u8,
                if enable { 0xFFFF } else { 0 },
                self.usb_interface as u16,
                &[],
            )
            .context("Setting break condition")?;
        Ok(())
    }

    fn borrow_fd(&self) -> Result<BorrowedFd<'_>> {
        self.serial_port.borrow_fd()
    }
}
