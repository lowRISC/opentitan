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
use serde_annotate::serialize;
use serde_annotate::Annotate;
use serde_annotate::Base;

use opentitanlib::app::command::CommandDispatch;
use opentitanlib::app::TransportWrapper;
use opentitanlib::crypto::ecdsa::EcdsaPrivateKey;
use opentitanlib::otp::otp_img::{OtpImg, OtpImgItem, OtpImgPartition, OtpImgValue};
use opentitanlib::rom_patch::RomPatchPartition;
use opentitanlib::rom_patch::N_MATCH_DESCRIPTORS;

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
        short = 'o',
        long,
        name = "OUTPUT_PATH",
        help = "Path to the HJSON-formatted output for the generated ROM patch partition"
    )]
    output: Option<PathBuf>,
}

impl CommandDispatch for Generate {
    fn run(
        &self,
        _context: &dyn Any,
        _transport: &TransportWrapper,
    ) -> Result<Option<Box<dyn Annotate>>> {
        let private_key = EcdsaPrivateKey::load(&self.key)?;
        let patch_partition: RomPatchPartition<N_MATCH_DESCRIPTORS> =
            RomPatchPartition::new(&self.patch, &private_key)?;

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

        if let Some(output) = &self.output {
            let mut file = File::create(output)?;
            file.write_all(
                serialize(&otp_img)?
                    .to_json()
                    .bases(&[Base::Hex])
                    .to_string()
                    .as_bytes(),
            )?;
            Ok(None)
        } else {
            Ok(Some(Box::new(otp_img)))
        }
    }
}

#[derive(Debug, Subcommand, CommandDispatch)]
/// ROM patch related commands.
pub enum RomPatch {
    Generate(Generate),
}
