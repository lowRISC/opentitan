// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use std::any::Any;
use std::fs::File;
use std::io::Write;
use std::path::PathBuf;

use anyhow::Result;

use serde_annotate::{serialize, Annotate, Base};

use clap::{Args, Subcommand};

use opentitanlib::app::command::CommandDispatch;
use opentitanlib::app::TransportWrapper;
use opentitanlib::otp::alert_handler::AlertRegs;
use opentitanlib::otp::lc_state::LcStateVal;
use opentitanlib::otp::otp_img::{OtpImg, OtpImgItem, OtpImgPartition, OtpImgValue};

/// Generate CRC magic value for alert_handler configuration.
#[derive(Debug, Args)]
pub struct AlertDigest {
    /// OTP memory map file containing alert_handler config in HJSON format.
    alert_cfg: PathBuf,
    /// Output file to write the new OTP overlay to instead of printing.
    #[arg(long)]
    output: Option<PathBuf>,
    /// Override switch to specify a custom partition.
    #[arg(long, default_value = "OWNER_SW_CFG")]
    partition: String,
}

impl CommandDispatch for AlertDigest {
    fn run(
        &self,
        _context: &dyn Any,
        _transport: &TransportWrapper,
    ) -> Result<Option<Box<dyn Annotate>>> {
        // From kErrorOk in ROM.
        const ERROR_OK: u32 = 0x739;

        // Life cycle states to generate digests for.
        let lc_states = [
            ("OWNER_SW_CFG_ROM_ALERT_DIGEST_PROD", LcStateVal::Prod),
            (
                "OWNER_SW_CFG_ROM_ALERT_DIGEST_PROD_END",
                LcStateVal::ProdEnd,
            ),
            ("OWNER_SW_CFG_ROM_ALERT_DIGEST_DEV", LcStateVal::Dev),
            ("OWNER_SW_CFG_ROM_ALERT_DIGEST_RMA", LcStateVal::Rma),
        ];

        // Read in the OTP img description.
        let otp = OtpImg::from_file(&self.alert_cfg)?;

        let mut items = Vec::<OtpImgItem>::new();

        for lc_state in lc_states {
            // Create model for alert_handler register states.
            let alert = AlertRegs::try_new(lc_state.1, &otp)?;

            // Use alert_handler registers states to construct CRC32 checksum.
            let crc32 = alert.crc32();

            // Match digest format expected by ROM.
            let digest = crc32 ^ lc_state.1 as u32 ^ ERROR_OK;

            items.push(OtpImgItem {
                name: lc_state.0.to_owned(),
                value: OtpImgValue::Word(digest as u64),
            });
        }

        // Construct OTP image overlay.
        let img_out = OtpImg {
            seed: None,
            partitions: vec![OtpImgPartition {
                name: self.partition.clone(),
                items: Some(items),
            }],
        };

        if let Some(output) = &self.output {
            let mut file = File::create(output)?;
            file.write_all(
                serialize(&img_out)?
                    .to_json()
                    .bases(&[Base::Hex])
                    .to_string()
                    .as_bytes(),
            )?;
            Ok(None)
        } else {
            Ok(Some(Box::new(img_out)))
        }
    }
}

#[derive(Debug, Subcommand, CommandDispatch)]
/// OTP related commands.
pub enum Otp {
    AlertDigest(AlertDigest),
}
