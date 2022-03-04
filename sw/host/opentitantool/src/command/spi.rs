// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::Result;
use erased_serde::Serialize;
use indicatif::{ProgressBar, ProgressStyle};
use std::any::Any;
use std::fs::{self, File};
use std::io::{self, Write};
use std::path::PathBuf;
use std::time::Instant;
use structopt::StructOpt;

use opentitanlib::app::command::CommandDispatch;
use opentitanlib::app::TransportWrapper;
use opentitanlib::io::spi::{SpiParams, Transfer};
use opentitanlib::spiflash::SpiFlash;
use opentitanlib::transport::Capability;

/// Read and parse an SFDP table.
#[derive(Debug, StructOpt)]
pub struct SpiSfdp {
    #[structopt(
        short,
        long,
        help = "Display raw SFDP bytes rather than the parsed struct."
    )]
    raw: Option<usize>,
}

// Print a hexdump of a buffer to `writer`.
// The hexdump includes the offset, hex bytes and printable ASCII characters.
//
//  00000000: 53 46 44 50 06 01 02 ff 00 06 01 10 30 00 00 ff  SFDP........0...
//  00000010: c2 00 01 04 10 01 00 ff 84 00 01 02 c0 00 00 ff  ................
//  00000020: ff ff ff ff ff ff ff ff ff ff ff ff ff ff ff ff  ................
//  00000030: e5 20 fb ff ff ff ff 3f 44 eb 08 6b 08 3b 04 bb  . .....?D..k.;..
//
// Note: This format can be consumed by `xxd -r` and converted back into binary.
fn hexdump(mut writer: impl Write, buf: &[u8]) -> Result<()> {
    for (i, chunk) in buf.chunks(16).enumerate() {
        let mut ascii = [b'.'; 16];
        write!(writer, "{:08x}:", i * 16)?;
        for (j, byte) in chunk.iter().copied().enumerate() {
            write!(writer, " {:02x}", byte)?;
            // For printable ASCII chars, place them in the ascii buffer.
            if byte == b' ' || byte.is_ascii_graphic() {
                ascii[j] = byte;
            }
        }
        // Align and print the ascii buffer.
        let j = chunk.len();
        for _ in 0..(16 - j) {
            write!(writer, "   ")?;
        }
        writeln!(writer, "  {}", std::str::from_utf8(&ascii[0..j]).unwrap())?;
    }
    Ok(())
}

// Helper function to create a progress bar in the same form for each of
// the commands which will use it.
fn progress_bar(total: u64) -> ProgressBar {
    let progress = ProgressBar::new(total);
    progress.set_style(
        ProgressStyle::default_bar()
            .template("[{elapsed_precise}] [{wide_bar}] {bytes}/{total_bytes} ({eta})"),
    );
    progress
}

impl CommandDispatch for SpiSfdp {
    fn run(
        &self,
        context: &dyn Any,
        transport: &TransportWrapper,
    ) -> Result<Option<Box<dyn Serialize>>> {
        transport.capabilities()?.request(Capability::SPI).ok()?;
        let context = context.downcast_ref::<SpiCommand>().unwrap();
        let spi = context.params.create(transport)?;

        if let Some(length) = self.raw {
            let mut buffer = vec![0u8; length];
            spi.run_transaction(&mut [
                Transfer::Write(&[SpiFlash::READ_SFDP, 0, 0, 0, 0]),
                Transfer::Read(&mut buffer),
            ])?;
            hexdump(io::stdout(), &buffer)?;
            Ok(None)
        } else {
            let sfdp = SpiFlash::read_sfdp(&*spi)?;
            Ok(Some(Box::new(sfdp)))
        }
    }
}

/// Read the JEDEC ID of a SPI EEPROM.
#[derive(Debug, StructOpt)]
pub struct SpiReadId {
    #[structopt(
        short = "n",
        long,
        default_value = "3",
        help = "Number of JEDEC ID bytes to read."
    )]
    length: usize,
}

#[derive(Debug, serde::Serialize)]
pub struct SpiReadIdResponse {
    jedec_id: Vec<u8>,
}

impl CommandDispatch for SpiReadId {
    fn run(
        &self,
        context: &dyn Any,
        transport: &TransportWrapper,
    ) -> Result<Option<Box<dyn Serialize>>> {
        transport.capabilities()?.request(Capability::SPI).ok()?;
        let context = context.downcast_ref::<SpiCommand>().unwrap();
        let spi = context.params.create(transport)?;
        let jedec_id = SpiFlash::read_jedec_id(&*spi, self.length)?;
        Ok(Some(Box::new(SpiReadIdResponse { jedec_id })))
    }
}

/// Read data from a SPI EEPROM.
#[derive(Debug, StructOpt)]
pub struct SpiRead {
    #[structopt(short, long, default_value = "0", help = "Start offset.")]
    start: u32,
    #[structopt(
        short = "n",
        long,
        default_value = "4096",
        help = "Number of bytes to read."
    )]
    length: usize,
    #[structopt(short, long, help = "Hexdump the data.")]
    hexdump: bool,
    #[structopt(name = "FILE", default_value = "-")]
    filename: PathBuf,
}

#[derive(Debug, serde::Serialize)]
pub struct SpiReadResponse {
    length: usize,
    bytes_per_second: f64,
}

impl SpiRead {
    fn write_file(&self, mut writer: impl Write, buffer: &[u8]) -> Result<()> {
        if self.hexdump {
            hexdump(writer, buffer)?;
        } else {
            writer.write_all(buffer)?;
        }
        Ok(())
    }
}

impl CommandDispatch for SpiRead {
    fn run(
        &self,
        context: &dyn Any,
        transport: &TransportWrapper,
    ) -> Result<Option<Box<dyn Serialize>>> {
        transport.capabilities()?.request(Capability::SPI).ok()?;
        let context = context.downcast_ref::<SpiCommand>().unwrap();
        let spi = context.params.create(transport)?;
        let mut flash = SpiFlash::from_spi(&*spi)?;
        flash.set_address_mode_auto(&*spi)?;

        let mut buffer = vec![0u8; self.length];
        let progress = progress_bar(self.length as u64);
        let t0 = Instant::now();
        flash.read_with_progress(&*spi, self.start, &mut buffer, |_, chunk| {
            progress.inc(chunk as u64);
        })?;
        progress.finish();
        let duration = t0.elapsed().as_secs_f64();

        if self.filename.to_str() == Some("-") {
            self.write_file(io::stdout(), &buffer)?;
            Ok(None)
        } else {
            let file = File::create(&self.filename)?;
            self.write_file(file, &buffer)?;
            Ok(Some(Box::new(SpiReadResponse {
                length: buffer.len(),
                bytes_per_second: buffer.len() as f64 / duration,
            })))
        }
    }
}

/// Erase sectors of a SPI EEPROM.
#[derive(Debug, StructOpt)]
pub struct SpiErase {
    #[structopt(short, long, help = "Start offset.")]
    start: u32,
    #[structopt(short = "n", long, help = "Number of bytes to erase.")]
    length: u32,
}

#[derive(Debug, serde::Serialize)]
pub struct SpiEraseResponse {
    length: u32,
    bytes_per_second: f64,
}

impl CommandDispatch for SpiErase {
    fn run(
        &self,
        context: &dyn Any,
        transport: &TransportWrapper,
    ) -> Result<Option<Box<dyn Serialize>>> {
        transport.capabilities()?.request(Capability::SPI).ok()?;
        let context = context.downcast_ref::<SpiCommand>().unwrap();
        let spi = context.params.create(transport)?;
        let mut flash = SpiFlash::from_spi(&*spi)?;
        flash.set_address_mode_auto(&*spi)?;

        let progress = progress_bar(self.length as u64);
        let t0 = Instant::now();
        flash.erase_with_progress(&*spi, self.start, self.length, |_, chunk| {
            progress.inc(chunk as u64);
        })?;
        progress.finish();
        let duration = t0.elapsed().as_secs_f64();

        Ok(Some(Box::new(SpiEraseResponse {
            length: self.length,
            bytes_per_second: self.length as f64 / duration,
        })))
    }
}

/// Program data into a SPI EEPROM.
#[derive(Debug, StructOpt)]
pub struct SpiProgram {
    #[structopt(short, long, default_value = "0", help = "Start offset.")]
    start: u32,
    #[structopt(name = "FILE")]
    filename: PathBuf,
}

#[derive(Debug, serde::Serialize)]
pub struct SpiProgramResponse {
    length: usize,
    bytes_per_second: f64,
}

impl CommandDispatch for SpiProgram {
    fn run(
        &self,
        context: &dyn Any,
        transport: &TransportWrapper,
    ) -> Result<Option<Box<dyn Serialize>>> {
        transport.capabilities()?.request(Capability::SPI).ok()?;
        let context = context.downcast_ref::<SpiCommand>().unwrap();
        let spi = context.params.create(transport)?;
        let mut flash = SpiFlash::from_spi(&*spi)?;
        flash.set_address_mode_auto(&*spi)?;

        let buffer = fs::read(&self.filename)?;
        let progress = progress_bar(buffer.len() as u64);
        let t0 = Instant::now();
        flash.program_with_progress(&*spi, self.start, &buffer, |_, chunk| {
            progress.inc(chunk as u64);
        })?;
        progress.finish();
        let duration = t0.elapsed().as_secs_f64();

        Ok(Some(Box::new(SpiProgramResponse {
            length: buffer.len(),
            bytes_per_second: buffer.len() as f64 / duration,
        })))
    }
}

/// Commands for interacting with a SPI EEPROM.
#[derive(Debug, StructOpt, CommandDispatch)]
pub enum InternalSpiCommand {
    Sfdp(SpiSfdp),
    ReadId(SpiReadId),
    Read(SpiRead),
    Erase(SpiErase),
    Program(SpiProgram),
}

#[derive(Debug, StructOpt)]
pub struct SpiCommand {
    #[structopt(flatten)]
    params: SpiParams,

    #[structopt(subcommand)]
    command: InternalSpiCommand,
}

impl CommandDispatch for SpiCommand {
    fn run(
        &self,
        _context: &dyn Any,
        transport: &TransportWrapper,
    ) -> Result<Option<Box<dyn Serialize>>> {
        // None of the SPI commands care about the prior context, but they do
        // care about the `bus` parameter in the current node.
        self.command.run(self, transport)
    }
}
