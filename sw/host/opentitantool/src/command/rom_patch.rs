// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::Result;
use log::*;
use serde_annotate::Annotate;
use std::any::Any;
use std::io::Read;
use std::path::PathBuf;
use structopt::StructOpt;

use opentitanlib::app::command::CommandDispatch;
use opentitanlib::app::TransportWrapper;
use opentitanlib::crypto::rsa::RsaPrivateKey;
use opentitanlib::rom_patch::patch::RomPatchPartition;

/// Generate an OTP ROM patch partition
#[derive(Debug, StructOpt)]
pub struct Generate {
    #[structopt(
        short = "p",
        long = "patch",
        name = "HJSON_FILE",
        help = "HJSON formatted ROM patch description file"
    )]
    patch: PathBuf,

    #[structopt(
        short = "k", long = "key",
        name = "DER_FILE",
        parse(try_from_str=RsaPrivateKey::from_pkcs8_der_file),
        help = "RSA private key file in PKCS#1 DER format"
    )]
    key: RsaPrivateKey,

    #[structopt(
        short = "s",
        long = "otp_size",
        name = "OTP_SIZE",
        help = "OTP ROM patch partition total size (bytes)"
    )]
    otp_size: usize,
}

impl CommandDispatch for Generate {
    fn run(
        &self,
        _context: &dyn Any,
        _transport: &TransportWrapper,
    ) -> Result<Option<Box<dyn Annotate>>> {
        let mut patch_partition = RomPatchPartition::new(&self.patch, &self.key)?;
        let mut buffer = vec![0_u8; self.otp_size];
        _ = patch_partition.read(&mut buffer)?;

        println!("uint8_t fake_patch[] =");
        print!("{{ ");
        for (i, b) in buffer.iter().enumerate() {
            if i % 4 == 0 {
                if i != 0 {
                    print!("// [{:#010x}] ", i - 4);
                }
                print!("\n\t ");
            }

            print!("{:#04x}, ", b);
        }
        println!("}};");

        debug!(
            "OTP patch partition {} bytes\n{}",
            patch_partition.len(),
            patch_partition
        );

        Ok(None)
    }
}

#[derive(Debug, StructOpt, CommandDispatch)]
/// ROM patch related commands.
pub enum RomPatch {
    Generate(Generate),
}
