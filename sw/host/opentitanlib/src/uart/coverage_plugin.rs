// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::{Result, bail};
use crc::{CRC_32_ISO_HDLC, Crc};
use log;
use rand::Rng;

use crate::uart::console::ExitStatus;
use crate::uart::console_plugin::ConsolePlugin;

const COVERAGE_START_ANCHOR: &[u8] = b"\x10== COVERAGE PROFILE START ==\r\n";
const COVERAGE_END_ANCHOR: &[u8] = b"\x10== COVERAGE PROFILE END ==\r\n";
const COVERAGE_SKIP_ANCHOR: &[u8] = b"\x10== COVERAGE PROFILE SKIP ==\r\n";

#[derive(Default)]
pub struct CoveragePlugin {
    stop_after_report: bool,
    is_capturing: bool,
    buffer: Vec<u8>,
    exit_status: Option<ExitStatus>,
}

impl CoveragePlugin {
    pub fn stop_after_report(mut self) -> Self {
        self.stop_after_report = true;
        self
    }

    fn save_coverage_data(&mut self) -> Result<()> {
        let response = hex::decode(&self.buffer)?;
        if response.len() < 4 {
            bail!(
                "Coverage from the device is too short: {} bytes",
                response.len()
            );
        }

        let (response, crc) = response.split_at(response.len() - 4);
        let crc = u32::from_le_bytes(crc.try_into()?);
        let actual = Crc::<u32>::new(&CRC_32_ISO_HDLC).checksum(response);
        if crc != actual {
            bail!("Coverage corrupted: crc = {crc:08x}, actual = {actual:08x}");
        }

        let path = std::env::var("LLVM_PROFILE_FILE").unwrap_or("./default.profraw".to_owned());
        let path = path.replace("%h", "test.on.device");
        let path = path.replace("%p", &rand::thread_rng().r#gen::<u32>().to_string());
        let path = path.replace("%m", "0");
        let path = path.replace(".profraw", ".xprofraw");

        log::info!("Saving coverage profile to {path}");
        std::fs::write(path, response)?;

        Ok(())
    }

    fn report_received(&mut self) {
        if self.stop_after_report {
            log::info!("Stop console after receiving coverage report.");
            self.exit_status = Some(ExitStatus::ExitSuccess);
        }
    }
}

impl ConsolePlugin for CoveragePlugin {
    fn process_bytes(&mut self, bytes: Vec<u8>) -> Result<Vec<u8>> {
        // Process each byte with `process_byte`, and return the accumulated results.
        let mut passthrough = Vec::new();
        for byte in bytes {
            self.buffer.push(byte);
            if self.buffer.ends_with(COVERAGE_START_ANCHOR) {
                if self.is_capturing {
                    log::warn!("Got unterminated coverage block, starting new one.");
                } else {
                    log::info!("Coverage capture started.");
                }
                self.is_capturing = true;
                self.buffer.clear();
            } else if self.buffer.ends_with(COVERAGE_END_ANCHOR) {
                if self.is_capturing {
                    self.buffer
                        .truncate(self.buffer.len() - COVERAGE_END_ANCHOR.len());
                    self.save_coverage_data()?;
                    log::info!("Coverage capture ended.");
                } else {
                    log::warn!("Got unexpected coverage end indicator!");
                }
                self.is_capturing = false;
                self.buffer.clear();
                self.report_received();
            } else if self.buffer.ends_with(COVERAGE_SKIP_ANCHOR) {
                if self.is_capturing {
                    log::warn!("Got unterminated coverage block, skipping it.");
                } else {
                    log::info!("Coverage capture skipped.");
                }
                self.is_capturing = false;
                self.buffer.clear();
                self.report_received();
            } else if COVERAGE_START_ANCHOR.starts_with(&self.buffer)
                || COVERAGE_END_ANCHOR.starts_with(&self.buffer)
                || COVERAGE_SKIP_ANCHOR.starts_with(&self.buffer)
            {
                // The buffer is a prefix of an anchor, keep waiting.
            } else if !self.is_capturing {
                // Not an anchor prefix, flush the buffer.
                passthrough.extend(std::mem::take(&mut self.buffer));
                if byte == COVERAGE_START_ANCHOR[0] {
                    passthrough.pop();
                    self.buffer.push(byte)
                }
            } else {
                // Capturing.
            }
        }
        Ok(passthrough)
    }

    fn exit_status(&self) -> Option<ExitStatus> {
        self.exit_status
    }
}
