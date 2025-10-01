// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::Result;
use clap::Args;
use std::path::PathBuf;
use std::str::FromStr;

use super::{Backend, BackendOpts, define_interface};
use crate::transport::Transport;
use crate::transport::ti50emulator::Ti50Emulator;

#[derive(Debug, Args)]
pub struct Ti50EmulatorOpts {
    #[arg(long, default_value = "ti50")]
    instance_prefix: String,

    #[arg(long, value_parser = PathBuf::from_str, default_value = "")]
    executable_directory: PathBuf,

    #[arg(long, default_value = "")]
    executable: String,
}

struct Ti50EmulatorBackend;

impl Backend for Ti50EmulatorBackend {
    type Opts = Ti50EmulatorOpts;

    fn create_transport(_: &BackendOpts, args: &Ti50EmulatorOpts) -> Result<Box<dyn Transport>> {
        Ok(Box::new(Ti50Emulator::open(
            &args.executable_directory,
            &args.executable,
            &args.instance_prefix,
        )?))
    }
}

define_interface!(
    "ti50emulator",
    Ti50EmulatorBackend,
    "/__builtin__/ti50emulator.json5"
);
