// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::Result;
use clap::{Args, Subcommand};
use serde_annotate::Annotate;
use std::any::Any;
use std::fs::{self, File};
use std::io::{self, Write};
use std::path::PathBuf;
use std::time::Duration;

use opentitanlib::app::command::CommandDispatch;
use opentitanlib::app::{StagedProgressBar, TransportWrapper};
use opentitanlib::io::eeprom::{AddressMode, Transaction, MODE_111};
use opentitanlib::io::spi::{SpiParams, Transfer};
use opentitanlib::spiflash::{EraseMode, ReadMode, SpiFlash};
use opentitanlib::tpm;
use opentitanlib::transport::Capability;
use opentitanlib::transport::ProgressIndicator;
use opentitanlib::util::hexdump::hexdump;

/// Read and parse an SFDP table.
#[derive(Debug, Args)]
pub struct SpiSfdp {
    /// Display raw SFDP bytes rather than the parsed struct.
    #[arg(short, long)]
    raw: Option<usize>,

    /// Start reading SFDP at offset.  Only valid with --raw.
    #[arg(short, long)]
    offset: Option<u32>,
}

impl CommandDispatch for SpiSfdp {
    fn run(
        &self,
        context: &dyn Any,
        transport: &TransportWrapper,
    ) -> Result<Option<Box<dyn Annotate>>> {
        transport.capabilities()?.request(Capability::SPI).ok()?;
        let context = context.downcast_ref::<SpiCommand>().unwrap();
        let spi = context.params.create(transport, "BOOTSTRAP")?;

        if let Some(length) = self.raw {
            let offset = self.offset.unwrap_or(0);
            let mut buffer = vec![0u8; length];
            spi.run_eeprom_transactions(&mut [Transaction::Read(
                MODE_111
                    .dummy_cycles(8)
                    .cmd_addr(SpiFlash::READ_SFDP, offset, AddressMode::Mode3b),
                &mut buffer,
            )])?;
            hexdump(io::stdout(), &buffer)?;
            Ok(None)
        } else {
            let sfdp = SpiFlash::read_sfdp(&*spi)?;
            Ok(Some(Box::new(sfdp)))
        }
    }
}

/// Read the JEDEC ID of a SPI EEPROM.
#[derive(Debug, Args)]
pub struct SpiReadId {
    /// Number of JEDEC ID bytes to read.
    #[arg(short = 'n', long, default_value = "15")]
    length: usize,
}

#[derive(Debug, serde::Serialize, Annotate)]
pub struct SpiReadIdResponse {
    #[annotate(format = hex)]
    jedec_id: Vec<u8>,
}

impl CommandDispatch for SpiReadId {
    fn run(
        &self,
        context: &dyn Any,
        transport: &TransportWrapper,
    ) -> Result<Option<Box<dyn Annotate>>> {
        transport.capabilities()?.request(Capability::SPI).ok()?;
        let context = context.downcast_ref::<SpiCommand>().unwrap();
        let spi = context.params.create(transport, "BOOTSTRAP")?;
        let jedec_id = SpiFlash::read_jedec_id(&*spi, self.length)?;
        Ok(Some(Box::new(SpiReadIdResponse { jedec_id })))
    }
}

/// Read data from a SPI EEPROM.
#[derive(Debug, Args)]
pub struct SpiRead {
    /// Start offset.
    #[arg(short, long, default_value = "0")]
    start: u32,
    /// Number of bytes to read.
    #[arg(short = 'n', long, default_value = "4096")]
    length: usize,
    /// Read mode.
    #[arg(
        short,
        long,
        value_enum,
        ignore_case = true,
        default_value = "standard"
    )]
    pub mode: ReadMode,
    #[arg(short = '4', long, default_value = "false")]
    pub use_4b_opcodes: bool,
    /// Hexdump the data.
    #[arg(long)]
    hexdump: bool,
    #[arg(value_name = "FILE", default_value = "-")]
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
    ) -> Result<Option<Box<dyn Annotate>>> {
        transport.capabilities()?.request(Capability::SPI).ok()?;
        let context = context.downcast_ref::<SpiCommand>().unwrap();
        let spi = context.params.create(transport, "BOOTSTRAP")?;
        let mut flash = SpiFlash::from_spi(&*spi)?;
        flash.set_address_mode_auto(&*spi)?;
        flash.read_mode = self.mode;

        let mut buffer = vec![0u8; self.length];
        let progress = StagedProgressBar::new();
        flash.read_with_progress(
            &*spi,
            self.start,
            &mut buffer,
            &progress,
            self.use_4b_opcodes,
        )?;

        if self.filename.to_str() == Some("-") {
            self.write_file(io::stdout(), &buffer)?;
            Ok(None)
        } else {
            let file = File::create(&self.filename)?;
            self.write_file(file, &buffer)?;
            Ok(Some(Box::new(SpiReadResponse {
                length: buffer.len(),
                bytes_per_second: progress.bytes_per_second(),
            })))
        }
    }
}

/// Erase sectors of a SPI EEPROM.
#[derive(Debug, Args)]
pub struct SpiErase {
    /// Start offset.
    #[arg(short, long, required_unless_present = "chip")]
    start: Option<u32>,
    /// Number of bytes to erase.
    #[arg(short = 'n', long, required_unless_present = "chip")]
    length: Option<u32>,
    /// Erase the whole chip.
    #[arg(long)]
    chip: bool,
    /// Erase mode.
    #[arg(
        short,
        long,
        value_enum,
        ignore_case = true,
        default_value = "standard"
    )]
    pub mode: EraseMode,
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
    ) -> Result<Option<Box<dyn Annotate>>> {
        transport.capabilities()?.request(Capability::SPI).ok()?;
        let context = context.downcast_ref::<SpiCommand>().unwrap();
        let spi = context.params.create(transport, "BOOTSTRAP")?;
        let mut flash = SpiFlash::from_spi(&*spi)?;
        flash.set_address_mode_auto(&*spi)?;
        flash.erase_mode = self.mode;

        let (start, length) = if self.chip {
            (0, flash.size)
        } else {
            (self.start.unwrap(), self.length.unwrap())
        };

        let progress = StagedProgressBar::new();
        if self.chip {
            // Since we can't get any progress from chip_erase, be extra
            // helpful and set the progress bar to 99% complete and enable
            // the steady tick so the user can watch the seconds count up.
            progress.new_stage("", length as usize);
            progress.enable_steady_tick(Duration::from_secs(1));
            progress.progress(length as usize * 99 / 100);
            flash.chip_erase(&*spi)?;
        } else {
            flash.erase_with_progress(&*spi, start, length, &progress)?;
        }

        Ok(Some(Box::new(SpiEraseResponse {
            length,
            bytes_per_second: progress.bytes_per_second(),
        })))
    }
}

/// Program data into a SPI EEPROM.
#[derive(Debug, Args)]
pub struct SpiProgram {
    /// Start offset.
    #[arg(short, long, default_value = "0")]
    start: u32,
    #[arg(value_name = "FILE")]
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
    ) -> Result<Option<Box<dyn Annotate>>> {
        transport.capabilities()?.request(Capability::SPI).ok()?;
        let context = context.downcast_ref::<SpiCommand>().unwrap();
        let spi = context.params.create(transport, "BOOTSTRAP")?;
        let mut flash = SpiFlash::from_spi(&*spi)?;
        flash.set_address_mode_auto(&*spi)?;

        let buffer = fs::read(&self.filename)?;
        let progress = StagedProgressBar::new();
        flash.program_with_progress(&*spi, self.start, &buffer, &progress)?;

        Ok(Some(Box::new(SpiProgramResponse {
            length: buffer.len(),
            bytes_per_second: progress.bytes_per_second(),
        })))
    }
}

#[derive(Debug, Args)]
pub struct SpiTpm {
    #[command(subcommand)]
    command: super::tpm::TpmSubCommand,

    /// Pin used for signalling by Google security chips
    #[arg(long)]
    gsc_ready: Option<String>,
}

impl CommandDispatch for SpiTpm {
    fn run(
        &self,
        context: &dyn Any,
        transport: &TransportWrapper,
    ) -> Result<Option<Box<dyn Annotate>>> {
        let context = context.downcast_ref::<SpiCommand>().unwrap();
        let ready_pin = match &self.gsc_ready {
            Some(pin) => Some((transport.gpio_pin(pin)?, transport.gpio_monitoring()?)),
            None => None,
        };
        let tpm_driver: Box<dyn tpm::Driver> = Box::new(tpm::SpiDriver::new(
            context.params.create(transport, "TPM")?,
            ready_pin,
        )?);
        self.command.run(&tpm_driver, transport)
    }
}

/// Read plain data bytes from a SPI device (not necessarily SPI EEPROM/flash).
#[derive(Debug, Args)]
pub struct SpiRawRead {
    /// Number of bytes to read.
    #[arg(short = 'n', long)]
    length: usize,
}

#[derive(Debug, serde::Serialize)]
pub struct SpiRawReadResponse {
    hexdata: String,
}

impl CommandDispatch for SpiRawRead {
    fn run(
        &self,
        context: &dyn Any,
        transport: &TransportWrapper,
    ) -> Result<Option<Box<dyn Annotate>>> {
        transport.capabilities()?.request(Capability::SPI).ok()?;
        let context = context.downcast_ref::<SpiCommand>().unwrap();
        let spi_bus = context.params.create(transport, "BOOTSTRAP")?;
        let mut v = vec![0u8; self.length];
        spi_bus.run_transaction(&mut [Transfer::Read(&mut v)])?;
        Ok(Some(Box::new(SpiRawReadResponse {
            hexdata: hex::encode(v),
        })))
    }
}

/// Write plain data bytes to a SPI device (not necessarily SPI EEPROM/flash).
#[derive(Debug, Args)]
pub struct SpiRawWrite {
    /// Hex data bytes to write.
    #[arg(short = 'd', long)]
    hexdata: String,
}

impl CommandDispatch for SpiRawWrite {
    fn run(
        &self,
        context: &dyn Any,
        transport: &TransportWrapper,
    ) -> Result<Option<Box<dyn Annotate>>> {
        transport.capabilities()?.request(Capability::SPI).ok()?;
        let context = context.downcast_ref::<SpiCommand>().unwrap();
        let spi_bus = context.params.create(transport, "BOOTSTRAP")?;
        spi_bus.run_transaction(&mut [Transfer::Write(&hex::decode(&self.hexdata)?)])?;
        Ok(None)
    }
}

/// Write data bytes to a SPI device then read data (not necessarily SPI EEPROM/flash).
#[derive(Debug, Args)]
pub struct SpiRawWriteRead {
    /// Hex data bytes to write.
    #[arg(short = 'd', long)]
    hexdata: String,

    /// Number of bytes to read.
    #[arg(short = 'n', long)]
    length: usize,
}

impl CommandDispatch for SpiRawWriteRead {
    fn run(
        &self,
        context: &dyn Any,
        transport: &TransportWrapper,
    ) -> Result<Option<Box<dyn Annotate>>> {
        transport.capabilities()?.request(Capability::SPI).ok()?;
        let context = context.downcast_ref::<SpiCommand>().unwrap();
        let spi_bus = context.params.create(transport, "BOOTSTRAP")?;
        let mut v = vec![0u8; self.length];
        spi_bus.run_transaction(&mut [
            Transfer::Write(&hex::decode(&self.hexdata)?),
            Transfer::Read(&mut v),
        ])?;
        Ok(Some(Box::new(SpiRawReadResponse {
            hexdata: hex::encode(v),
        })))
    }
}

/// Simultaneously write and read plain data bytes to a SPI device (not SPI EEPROM/flash).
#[derive(Debug, Args)]
pub struct SpiRawTransceive {
    /// Hex data bytes to write.
    #[arg(short = 'd', long)]
    hexdata: String,
}

impl CommandDispatch for SpiRawTransceive {
    fn run(
        &self,
        context: &dyn Any,
        transport: &TransportWrapper,
    ) -> Result<Option<Box<dyn Annotate>>> {
        transport.capabilities()?.request(Capability::SPI).ok()?;
        let context = context.downcast_ref::<SpiCommand>().unwrap();
        let spi_bus = context.params.create(transport, "BOOTSTRAP")?;
        let write_data = hex::decode(&self.hexdata)?;
        let mut read_data = vec![0u8; write_data.len()];
        spi_bus.run_transaction(&mut [Transfer::Both(&write_data, &mut read_data)])?;
        Ok(Some(Box::new(SpiRawReadResponse {
            hexdata: hex::encode(read_data),
        })))
    }
}

/// Commands for interacting with a SPI EEPROM.
#[derive(Debug, Subcommand, CommandDispatch)]
pub enum InternalSpiCommand {
    Sfdp(SpiSfdp),
    ReadId(SpiReadId),
    Read(SpiRead),
    Erase(SpiErase),
    Program(SpiProgram),
    RawRead(SpiRawRead),
    RawWrite(SpiRawWrite),
    RawWriteRead(SpiRawWriteRead),
    RawTransceive(SpiRawTransceive),
    Tpm(SpiTpm),
}

#[derive(Debug, Args)]
pub struct SpiCommand {
    #[command(flatten)]
    params: SpiParams,

    #[command(subcommand)]
    command: InternalSpiCommand,
}

impl CommandDispatch for SpiCommand {
    fn run(
        &self,
        _context: &dyn Any,
        transport: &TransportWrapper,
    ) -> Result<Option<Box<dyn Annotate>>> {
        // None of the SPI commands care about the prior context, but they do
        // care about the `bus` parameter in the current node.
        self.command.run(self, transport)
    }
}
