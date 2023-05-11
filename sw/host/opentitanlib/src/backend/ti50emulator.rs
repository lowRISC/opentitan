// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use crate::transport::ti50emulator::Ti50Emulator;
use crate::transport::Transport;
use anyhow::Result;
use clap::Args;
use std::path::{Path, PathBuf};

#[derive(Debug, Args)]
pub struct Ti50EmulatorOpts {
    #[arg(long, default_value = "ti50")]
    instance_prefix: String,

    #[arg(long)]
    executable_directory: Option<PathBuf>,

    #[arg(long, default_value = "")]
    executable: String,
}

pub fn create(args: &Ti50EmulatorOpts) -> Result<Box<dyn Transport>> {
    Ok(Box::new(Ti50Emulator::open(
        match args.executable_directory {
            None => Path::new(""),
            Some(ref path) => path,
        },
        &args.executable,
        &args.instance_prefix,
    )?))
}
