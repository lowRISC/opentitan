// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use std::any::Any;
use std::fs::File;
use std::io::Write;
use std::path::PathBuf;

use anyhow::Result;
use clap::Args;
use clap::Subcommand;
use log::*;
use serde_annotate::serialize;
use serde_annotate::Annotate;

use opentitanlib::app::command::CommandDispatch;
use opentitanlib::app::TransportWrapper;
use opentitanlib::crypto::ecdsa::EcdsaPrivateKey;
use opentitanlib::otp::otp_img::{OtpImg, OtpImgItem, OtpImgPartition, OtpImgValue};
use opentitanlib::rom_patch::RomPatchPartition;
use opentitanlib::util::file::ToWriter;

/// Generate an OTP ROM patch partition
#[derive(Debug, Args)]
pub struct Generate {
    #[arg(
        short = 'd',
        long = "description",
        name = "PATCH_DESC_FILE",
        help = "HJSON-formatted ROM patch description file"
    )]
    patch: PathBuf,

    #[arg(
        short = 'k',
        long = "key",
        name = "DER_FILE",
        help = "ECDSA private key file in PKCS#1 DER format"
    )]
    key: PathBuf,

    #[arg(
        short,
        long = "binary-output",
        name = "BINARY_OUTPUT_PATH",
        help = "Path to the binary output for the generated ROM patch partition"
    )]
    binary_output: Option<PathBuf>,

    #[arg(
        short = 'j',
        long,
        name = "HJSON_OUTPUT_PATH",
        help = "Path to the HJSON-formatted output for the generated ROM patch partition"
    )]
    hjson_output: Option<PathBuf>,
}

impl CommandDispatch for Generate {
    fn run(
        &self,
        _context: &dyn Any,
        _transport: &TransportWrapper,
    ) -> Result<Option<Box<dyn Annotate>>> {
        let private_key = EcdsaPrivateKey::load(&self.key)?;
        let patch_partition = RomPatchPartition::new(&self.patch, &private_key)?;

        let otp_img = OtpImg {
            seed: None,
            partitions: vec![OtpImgPartition {
                name: "ROM_PATCH".to_owned(),
                items: Some(vec![OtpImgItem {
                    name: "ROM_PATCH_DATA".to_owned(),
                    value: OtpImgValue::Sequence(patch_partition.as_vec()?),
                }]),
            }],
        };

        let json = serialize(&otp_img)?.to_hjson().to_string();

        if let Some(hjson_output) = &self.hjson_output {
            let mut file = File::create(hjson_output)?;
            file.write_all(&json.clone().into_bytes())?;
        }

        if let Some(binary_output) = &self.binary_output {
            patch_partition.clone().write_to_file(binary_output)?;
        }

        debug!("OTP HJSON: {}", json);

        Ok(None)
    }
}

#[derive(Debug, Subcommand, CommandDispatch)]
/// ROM patch related commands.
pub enum RomPatch {
    Generate(Generate),
}
