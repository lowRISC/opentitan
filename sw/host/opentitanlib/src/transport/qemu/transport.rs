// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use std::rc::Rc;

use anyhow::{ensure, Result};
use once_cell::sync::OnceCell;

use crate::io::uart::Uart;
use crate::transport::common::uart::FileUart;
use crate::transport::qemu::subprocess::{Options, Subprocess};
use crate::transport::{
    Capabilities, Capability, Transport, TransportError, TransportInterfaceType,
};

/// Represents the qemu transport object.
pub struct Qemu {
    subprocess: Subprocess,
    uart: OnceCell<Rc<FileUart>>,
}

impl Qemu {
    /// Creates a qemu subprocess-hosting transport from `options`.
    pub fn from_options(options: Options) -> Result<Self> {
        // Start the QEMU subprocess.
        let subprocess = Subprocess::from_options(options)?;

        Ok(Qemu {
            subprocess,
            uart: OnceCell::new(),
        })
    }

    /// Shuts down the qemu subprocess.
    pub fn shutdown(&mut self) -> Result<()> {
        self.subprocess.kill()
    }
}

impl Drop for Qemu {
    fn drop(&mut self) {
        self.shutdown().expect("failed to kill qemu subprocess");
    }
}

impl Transport for Qemu {
    fn capabilities(&self) -> Result<Capabilities> {
        Ok(Capabilities::new(Capability::UART))
    }

    fn uart(&self, instance: &str) -> Result<Rc<dyn Uart>> {
        const BAUD_RATE: u32 = 7200;

        ensure!(
            instance == "0",
            TransportError::InvalidInstance(TransportInterfaceType::Uart, instance.to_string())
        );

        let uart_path = self.subprocess.uart_path();
        let uart = self
            .uart
            .get_or_try_init(|| FileUart::open(uart_path, BAUD_RATE).map(Rc::new))?;

        Ok(uart.clone())
    }
}
