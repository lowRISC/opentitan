// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::Result;
use std::time::Duration;

use crate::app::TransportWrapper;
use crate::io::gpio::GpioPin;
use crate::io::uart::Uart;
use crate::transport::ProgressIndicator;
use crate::util::rom_detect::RomDetect;

/// Command for Transport::dispatch().
pub struct FpgaProgram<'a> {
    /// The bitstream content to load into the FPGA.
    pub bitstream: Vec<u8>,
    /// How long of a reset pulse to send to the device.
    pub rom_reset_pulse: Duration,
    /// How long to wait for the ROM to print its type and version.
    pub rom_timeout: Duration,
    /// A progress function to provide user feedback.
    /// Will be called with the address and length of each chunk sent to the target device.
    pub progress: Box<dyn ProgressIndicator + 'a>,
}

impl FpgaProgram<'_> {
    fn check_correct_version(&self, uart: &dyn Uart, reset_pin: &dyn GpioPin) -> Result<bool> {
        let mut rd = RomDetect::new(&self.bitstream, Some(self.rom_timeout))?;

        // Send a reset pulse so the ROM will print the FPGA version.
        // Reset is active low, sleep, then drive high.
        reset_pin.write(false)?;
        std::thread::sleep(self.rom_reset_pulse);
        // Also clear the UART RX buffer for improved robustness.
        uart.clear_rx_buffer()?;
        reset_pin.write(true)?;

        // Now read the uart until the ROM prints it's version.
        if rd.detect(uart)? {
            log::info!("Already running the correct bitstream.  Skip loading bitstream.");
            // If we're already running the right ROM+bitstream,
            // then we can skip bootstrap.
            return Ok(true);
        }
        Ok(false)
    }

    fn skip(&self) -> bool {
        self.bitstream.starts_with(b"__skip__")
    }

    pub fn should_skip(&self, transport: &TransportWrapper) -> Result<bool> {
        // Open the console UART.  We do this first so we get the receiver
        // started and the uart buffering data for us.
        let uart = transport.uart("CONSOLE")?;
        let reset_pin = transport.gpio_pin("RESET")?;
        if self.skip() {
            log::info!("Skip loading the __skip__ bitstream.");
            return Ok(true);
        }
        if self.check_correct_version(&*uart, &*reset_pin)? {
            return Ok(true);
        }
        Ok(false)
    }
}

/// Command for Transport::dispatch().
pub struct ClearBitstream;
