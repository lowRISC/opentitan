// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use std::any::Any;
use std::fs::File;
use std::io::Write;
use std::path::PathBuf;

use anyhow::{bail, Result};

use serde_annotate::{serialize, Annotate};

use structopt::StructOpt;

use opentitanlib::app::command::CommandDispatch;
use opentitanlib::app::TransportWrapper;
use opentitanlib::otp::alert_handler::AlertRegs;
use opentitanlib::otp::lc_state::LcStateVal;
use opentitanlib::otp::otp_img::{OtpImg, OtpImgItem, OtpImgPartition, OtpImgValue};

/// Generate CRC magic value for alert_handler configuration.
#[derive(Debug, StructOpt)]
pub struct AlertDigest {
    #[structopt(help = "OTP memory map file containing alert_handler config in HJSON format")]
    alert_cfg: PathBuf,
    #[structopt(help = r#"Life cycle state ("TEST", "DEV", "PROD", PROD_END, "RMA")"#)]
    lc_state: String,
    #[structopt(
        long,
        help = "Output file to write the new OTP overlay to instead of printing"
    )]
    output: Option<PathBuf>,
    #[structopt(
        long,
        default_value = "OWNER_SW_CFG",
        help = "Override switch to specify a custom partition"
    )]
    partition: String,
    #[structopt(long, help = "Override switch to specify a custom OTP item name")]
    name: Option<String>,
}

impl CommandDispatch for AlertDigest {
    fn run(
        &self,
        _context: &dyn Any,
        _transport: &TransportWrapper,
    ) -> Result<Option<Box<dyn Annotate>>> {
        // From kErrorOk in ROM.
        const ERROR_OK: u32 = 0x739;

        // Read in the OTP img description.
        let otp = OtpImg::from_file(&self.alert_cfg)?;

        let lc_str = self.lc_state.to_uppercase();
        let lc_state = match lc_str.as_ref() {
            "TEST" => LcStateVal::Test,
            "DEV" => LcStateVal::Dev,
            "PROD" => LcStateVal::Prod,
            "PROD_END" => LcStateVal::ProdEnd,
            "RMA" => LcStateVal::Rma,
            _ => bail!("invalid life cycle state {}", self.lc_state),
        };

        // Create model for alert_handler register states.
        let alert = AlertRegs::try_new(lc_state, &otp)?;

        // Use alert_handler registers states to construct CRC32 checksum.
        let crc32 = alert.crc32();

        // Match digest format expected by ROM.
        let digest = crc32 ^ lc_state as u32 ^ ERROR_OK;

        let item_name = self
            .name
            .clone()
            .unwrap_or(format!("OWNER_SW_CFG_ROM_ALERT_DIGEST_{}", self.lc_state).to_string());

        // Construct OTP image overlay.
        let img_out = OtpImg {
            seed: None,
            partitions: vec![OtpImgPartition {
                name: self.partition.clone(),
                items: Some(vec![OtpImgItem {
                    name: item_name,
                    value: OtpImgValue::Word(digest as u64),
                }]),
            }],
        };

        if let Some(output) = &self.output {
            let mut file = File::create(&output)?;
            file.write_all(serialize(&img_out)?.to_json().to_string().as_bytes())?;
            Ok(None)
        } else {
            Ok(Some(Box::new(img_out)))
        }
    }
}

#[derive(Debug, StructOpt, CommandDispatch)]
/// OTP related commands.
pub enum Otp {
    AlertDigest(AlertDigest),
}
