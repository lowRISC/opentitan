// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::{Context, Result};
use clap::Args;
use serde_annotate::Annotate;
use std::any::Any;

use opentitanlib::app::command::CommandDispatch;
use opentitanlib::app::TransportWrapper;

#[derive(Debug, Args)]
/// Decode a raw status. Optionally accepts an ELF file to recover the filename.
pub struct BfvCommand {
    /// Hex BFV value as reported by device on failures.
    bfv: Vec<String>,
}

unsafe extern "C" {
    fn bfv_decoder(bfv: u32, buf: *mut u8, buf_size: usize) -> usize;
}

impl CommandDispatch for BfvCommand {
    fn run(
        &self,
        _context: &dyn Any,
        _transport: &TransportWrapper,
    ) -> Result<Option<Box<dyn Annotate>>> {
        for value in &self.bfv {
            // Decode status.
            let string_bfv = if value.starts_with("0x") {
                &value.as_str()[2..]
            } else {
                value.as_str()
            };

            let bfv = u32::from_str_radix(string_bfv, 16)
                .context(format!("\"{}\" is not a valid hex value", string_bfv))?;
            let mut text = [0u8; 80];
            // SAFETY:  the decodr function is guaranteed to size of the string
            // written into text.
            let size = unsafe { bfv_decoder(bfv, text.as_mut_ptr(), text.len()) };

            println!(
                "{:08x}: {}",
                bfv,
                std::str::from_utf8(&text[..size]).unwrap()
            );
        }
        // Separate command output from the next shell prompt.
        println!();
        Ok(None)
    }
}
