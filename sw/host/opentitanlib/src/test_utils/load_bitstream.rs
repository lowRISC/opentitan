// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::Result;
use erased_serde::Serialize;
use std::path::{Path, PathBuf};
use std::time::Duration;
use structopt::StructOpt;

use crate::app::{self, TransportWrapper};
use crate::transport::cw310;
use crate::util::rom_detect::RomKind;

/// Load a bitstream into the FPGA.
#[derive(Debug, StructOpt)]
pub struct LoadBitstream {
    #[structopt(long, help = "The bitstream to load for the test")]
    pub bitstream: Option<PathBuf>,

    #[structopt(
        long,
        possible_values = &RomKind::variants(),
        case_insensitive = true,
        help = "OpenTitan ROM type"
    )]
    pub rom_kind: Option<RomKind>,
    #[structopt(long, parse(try_from_str=humantime::parse_duration), default_value="50ms", help = "Duration of the reset pulse.")]
    pub rom_reset_pulse: Duration,
    #[structopt(long, parse(try_from_str=humantime::parse_duration), default_value="2s", help = "Duration of ROM detection timeout")]
    pub rom_timeout: Duration,
}

impl LoadBitstream {
    pub fn init(&self, transport: &TransportWrapper) -> Result<Option<Box<dyn Serialize>>> {
        if let Some(bitstream) = &self.bitstream {
            self.load(transport, bitstream)
        } else {
            Ok(None)
        }
    }

    pub fn load(
        &self,
        transport: &TransportWrapper,
        file: &Path,
    ) -> Result<Option<Box<dyn Serialize>>> {
        log::info!("Loading bitstream: {:?}", file);
        let payload = std::fs::read(file)?;
        let progress = app::progress_bar(payload.len() as u64);
        let pfunc = Box::new(move |_, chunk| {
            progress.inc(chunk as u64);
        });
        let operation = cw310::FpgaProgram {
            bitstream: payload,
            rom_kind: self.rom_kind,
            rom_reset_pulse: self.rom_reset_pulse,
            rom_timeout: self.rom_timeout,
            progress: Some(pfunc),
        };
        Ok(transport.dispatch(&operation)?)
    }
}
