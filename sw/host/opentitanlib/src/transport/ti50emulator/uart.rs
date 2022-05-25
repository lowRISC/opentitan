// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::Result;
use std::time::Duration;

use crate::io::uart::Uart;
use crate::transport::TransportError;

pub struct Ti50Uart {}

/// A trait which represents a UART.
impl Uart for Ti50Uart {
    /// Returns the UART baudrate.  May return zero for virtual UARTs.
    fn get_baudrate(&self) -> Result<u32> {
        Err(TransportError::UnsupportedOperation.into())
    }

    /// Sets the UART baudrate.  May do nothing for virtual UARTs.
    fn set_baudrate(&self, _baudrate: u32) -> Result<()> {
        Err(TransportError::UnsupportedOperation.into())
    }

    /// Reads UART receive data into `buf`, returning the number of bytes read.
    /// This function _may_ block.
    fn read(&self, _buf: &mut [u8]) -> Result<usize> {
        Err(TransportError::UnsupportedOperation.into())
    }

    /// Reads UART receive data into `buf`, returning the number of bytes read.
    /// The `timeout` may be used to specify a duration to wait for data.
    /// If timeout expires without any data arriving `Ok(0)` will be returned, never `Err(_)`.
    fn read_timeout(&self, _buf: &mut [u8], _timeout: Duration) -> Result<usize> {
        Err(TransportError::UnsupportedOperation.into())
    }

    /// Writes data from `buf` to the UART.
    fn write(&self, _buf: &[u8]) -> Result<()> {
        Err(TransportError::UnsupportedOperation.into())
    }
}
