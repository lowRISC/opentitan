// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::Result;
use clap::{Args, Subcommand, ValueEnum};
use serde_annotate::Annotate;
use std::any::Any;
use std::fs::{File, OpenOptions};
use std::path::PathBuf;

use opentitanlib::app::command::CommandDispatch;
use opentitanlib::app::TransportWrapper;
use opentitanlib::chip::helper::{OwnershipActivateParams, OwnershipUnlockParams};
use opentitanlib::crypto::ecdsa::{EcdsaPrivateKey, EcdsaRawSignature};
use opentitanlib::ownership::{OwnerBlock, TlvHeader};

#[derive(ValueEnum, Debug, Clone, Copy, PartialEq)]
enum Format {
    Auto,
    Text,
    Binary,
}

#[derive(Debug, Args)]
pub struct OwnershipConfigCommand {
    #[arg(long, help = "Use the basic ownership block", conflicts_with = "input")]
    basic: bool,
    #[arg(
        short,
        long,
        help = "A file containing an ownership config block",
        conflicts_with = "basic",
        required_unless_present("basic")
    )]
    input: Option<PathBuf>,
    #[arg(long, value_enum, default_value_t = Format::Auto, help = "Input format")]
    inform: Format,
    #[arg(long, help = "A path to a detached signature for the owner block")]
    pub signature: Option<PathBuf>,
    #[arg(long, help = "A path to a private key to sign the request")]
    pub sign: Option<PathBuf>,
    #[arg(help = "Binary output file path")]
    output: Option<PathBuf>,
}

impl CommandDispatch for OwnershipConfigCommand {
    fn run(
        &self,
        _context: &dyn Any,
        _transport: &TransportWrapper,
    ) -> Result<Option<Box<dyn Annotate>>> {
        let mut config = if self.basic {
            OwnerBlock::basic()
        } else {
            let input = std::fs::read(self.input.as_ref().unwrap())?;
            let mut inform = self.inform;
            if inform == Format::Auto {
                inform = match input[0] {
                    b'{' | b'#' | b'/' | b'\n' => Format::Text,
                    _ => Format::Binary,
                };
            }
            match inform {
                Format::Text => {
                    let text = std::str::from_utf8(&input)?;
                    serde_annotate::from_str::<OwnerBlock>(text)?
                }
                Format::Binary => {
                    let mut cursor = std::io::Cursor::new(&input);
                    let header = TlvHeader::read(&mut cursor)?;
                    OwnerBlock::read(&mut cursor, header)?
                }
                _ => unreachable!(),
            }
        };

        if let Some(signature) = &self.signature {
            let mut f = File::open(signature)?;
            config.signature = EcdsaRawSignature::read(&mut f)?;
        }
        if let Some(sign) = &self.sign {
            let key = EcdsaPrivateKey::load(sign)?;
            config.sign(&key)?;
        }

        if let Some(output) = &self.output {
            let mut f = OpenOptions::new().write(true).create(true).open(output)?;
            config.write(&mut f)?;
            Ok(None)
        } else {
            Ok(Some(Box::new(config)))
        }
    }
}

#[derive(Debug, Args)]
pub struct OwnershipUnlockCommand {
    #[command(flatten)]
    params: OwnershipUnlockParams,
    #[arg(short, long, help = "A file containing a binary unlock request")]
    input: Option<PathBuf>,
    #[arg(
        value_name = "FILE",
        help = "A file to write out a binary unlock request"
    )]
    output: Option<PathBuf>,
}

impl CommandDispatch for OwnershipUnlockCommand {
    fn run(
        &self,
        _context: &dyn Any,
        _transport: &TransportWrapper,
    ) -> Result<Option<Box<dyn Annotate>>> {
        let unlock = self
            .params
            .apply_to(self.input.as_ref().map(File::open).transpose()?.as_mut())?;
        if let Some(output) = &self.output {
            let mut f = OpenOptions::new()
                .write(true)
                .create(true)
                .truncate(true)
                .open(output)?;
            unlock.write(&mut f)?;
        }
        Ok(Some(Box::new(unlock)))
    }
}

#[derive(Debug, Args)]
pub struct OwnershipActivateCommand {
    #[command(flatten)]
    params: OwnershipActivateParams,
    #[arg(short, long, help = "A file containing a binary unlock request")]
    input: Option<PathBuf>,
    #[arg(
        value_name = "FILE",
        help = "A file to write out a binary unlock request"
    )]
    output: Option<PathBuf>,
}

impl CommandDispatch for OwnershipActivateCommand {
    fn run(
        &self,
        _context: &dyn Any,
        _transport: &TransportWrapper,
    ) -> Result<Option<Box<dyn Annotate>>> {
        let activate = self
            .params
            .apply_to(self.input.as_ref().map(File::open).transpose()?.as_mut())?;
        if let Some(output) = &self.output {
            let mut f = OpenOptions::new().write(true).create(true).open(output)?;
            activate.write(&mut f)?;
        }
        Ok(Some(Box::new(activate)))
    }
}

#[derive(Debug, Subcommand, CommandDispatch)]
pub enum OwnershipCommand {
    Config(OwnershipConfigCommand),
    Activate(OwnershipActivateCommand),
    Unlock(OwnershipUnlockCommand),
}
