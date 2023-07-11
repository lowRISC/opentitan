// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::{anyhow, Result};
use clap::{Args, Subcommand};
use serde::{Deserialize, Serialize};
use serde_annotate::Annotate;
use std::any::Any;

use opentitanlib::app::command::CommandDispatch;
use opentitanlib::app::TransportWrapper;
use opentitanlib::tpm;

/// Read the value of a given TPM register.
#[derive(Debug, Args)]
pub struct TpmReadRegister {
    #[arg(value_enum, ignore_case = true, help = "The TPM register to inspect")]
    register: tpm::Register,

    #[arg(long, help = "Number of bytes to read.")]
    length: Option<usize>,
}

#[derive(Annotate, Serialize, Deserialize, Debug, PartialEq, Eq)]
pub struct TpmReadRegisterResponse {
    hexdata: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    uint32: Option<u32>,
    #[serde(skip_serializing_if = "Option::is_none")]
    uint8: Option<u8>,
}

impl CommandDispatch for TpmReadRegister {
    fn run(
        &self,
        context: &dyn Any,
        _transport: &TransportWrapper,
    ) -> Result<Option<Box<dyn Annotate>>> {
        let tpm = context.downcast_ref::<Box<dyn tpm::Driver>>().unwrap();
        let length = self
            .length
            .or(self.register.size())
            .ok_or(anyhow!("Must specify --length"))?;
        let mut buffer = vec![0u8; length];
        tpm.read_register(self.register, &mut buffer)?;
        Ok(Some(Box::new(TpmReadRegisterResponse {
            hexdata: Option::Some(hex::encode(&buffer)),
            uint32: if buffer.len() == 4 {
                Some(u32::from_le_bytes([
                    buffer[0], buffer[1], buffer[2], buffer[3],
                ]))
            } else {
                Option::None
            },
            uint8: if buffer.len() == 1 {
                Some(buffer[0])
            } else {
                Option::None
            },
        })))
    }
}

/// Write to a given TPM register.
#[derive(Debug, Args)]
pub struct TpmWriteRegister {
    #[arg(value_enum, ignore_case = true, help = "The TPM register to modify")]
    register: tpm::Register,

    #[arg(
        short = 'd',
        long,
        conflicts_with_all=&["uint32", "uint8"],
        help = "Data to write, specify only one kind.",
    )]
    hexdata: Option<String>,
    #[arg(
        short = 'w',
        long,
        conflicts_with_all=&["hexdata", "uint8"],
        help = "Data to write, specify only one kind.",
    )]
    uint32: Option<u32>,
    #[arg(
        short = 'b',
        long,
        conflicts_with_all=&["hexdata", "uint32"],
        help = "Data to write, specify only one kind.",
    )]
    uint8: Option<u8>,
}

#[derive(Annotate, Serialize, Deserialize, Debug, PartialEq, Eq)]
pub struct TpmWriteRegisterResponse {}

impl CommandDispatch for TpmWriteRegister {
    fn run(
        &self,
        context: &dyn Any,
        _transport: &TransportWrapper,
    ) -> Result<Option<Box<dyn Annotate>>> {
        let tpm = context.downcast_ref::<Box<dyn tpm::Driver>>().unwrap();
        if let Some(hexdata) = &self.hexdata {
            tpm.write_register(self.register, &hex::decode(hexdata)?)?;
        } else if let Some(uint32) = self.uint32 {
            tpm.write_register(self.register, &u32::to_le_bytes(uint32))?;
        } else if let Some(uint8) = self.uint8 {
            tpm.write_register(self.register, &[uint8])?;
        }
        Ok(Some(Box::new(TpmWriteRegisterResponse {})))
    }
}

/// Write to a given TPM register.
#[derive(Debug, Args)]
pub struct TpmExecuteCommand {
    #[arg(short = 'd', long, help = "Hex encoding of TPM command to execute.")]
    hexdata: String,
}

#[derive(Annotate, Serialize, Deserialize, Debug, PartialEq, Eq)]
pub struct TpmExecuteCommandResponse {
    hexdata: String,
}

impl CommandDispatch for TpmExecuteCommand {
    fn run(
        &self,
        context: &dyn Any,
        _transport: &TransportWrapper,
    ) -> Result<Option<Box<dyn Annotate>>> {
        let tpm = context.downcast_ref::<Box<dyn tpm::Driver>>().unwrap();
        let resp = tpm.execute_command(&hex::decode(&self.hexdata)?)?;
        Ok(Some(Box::new(TpmExecuteCommandResponse {
            hexdata: hex::encode(resp),
        })))
    }
}

/// Commands for interacting with a TPM.  These appear as subcommands of both `opentitantool i2c
/// tpm` and `opentitantool spi tpm`.
#[derive(Debug, Subcommand, CommandDispatch)]
pub enum TpmSubCommand {
    ReadRegister(TpmReadRegister),
    WriteRegister(TpmWriteRegister),
    ExecuteCommand(TpmExecuteCommand),
}
