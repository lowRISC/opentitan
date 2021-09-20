// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use crate::transport::TransportError;
use anyhow::Result;
use serialport::{SerialPort, SerialPortType};
use std::cell::RefCell;
use std::rc::Rc;
use std::time::Duration;

use crate::io::uart::Uart;
use crate::transport::cw310::usb::Backend;

pub struct CW310Uart {
    port: RefCell<Box<dyn SerialPort>>,
}

impl CW310Uart {
    pub fn open(backend: Rc<RefCell<Backend>>, instance: u32) -> Result<Self> {
        let usb = backend.borrow();
        let serial_number = usb.get_serial_number();

        let mut ports = serialport::available_ports()?;
        ports.retain(|port| {
            if let SerialPortType::UsbPort(info) = &port.port_type {
                if info.serial_number.as_deref() == Some(serial_number) {
                    return true;
                }
            }
            false
        });
        // The CW board seems to have the last port connected as OpenTitan UART 0.
        // Reverse the sort order so the last port will be instance 0.
        ports.sort_by(|a, b| b.port_name.cmp(&a.port_name));

        let port = ports
            .get(instance as usize)
            .ok_or(TransportError::InvalidInstance("uart", instance))?;
        Ok(CW310Uart {
            port: RefCell::new(serialport::new(&port.port_name, 115200).open()?),
        })
    }
}

impl Uart for CW310Uart {
    /// Returns the UART baudrate.  May return zero for virtual UARTs.
    fn get_baudrate(&self) -> u32 {
        self.port.borrow().baud_rate().unwrap()
    }

    /// Sets the UART baudrate.  May do nothing for virtual UARTs.
    fn set_baudrate(&self, baudrate: u32) -> Result<()> {
        self.port.borrow_mut().set_baud_rate(baudrate)?;
        Ok(())
    }

    /// Reads UART receive data into `buf`, returning the number of bytes read.
    /// This function _may_ block.
    fn read(&self, buf: &mut [u8]) -> Result<usize> {
        Ok(self.port.borrow_mut().read(buf)?)
    }

    /// Reads UART receive data into `buf`, returning the number of bytes read.
    /// The `timeout` may be used to specify a duration to wait for data.
    fn read_timeout(&self, buf: &mut [u8], timeout: Duration) -> Result<usize> {
        let mut port = self.port.borrow_mut();
        port.set_timeout(timeout)?;
        let len = port.read(buf)?;
        port.set_timeout(Duration::MAX)?;
        Ok(len)
    }

    /// Writes data from `buf` to the UART.
    fn write(&self, buf: &[u8]) -> Result<usize> {
        Ok(self.port.borrow_mut().write(buf)?)
    }
}
