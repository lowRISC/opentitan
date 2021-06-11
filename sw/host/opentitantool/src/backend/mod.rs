// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::Result;
use structopt::StructOpt;
use thiserror::Error;

use opentitanlib::transport::{EmptyTransport, Transport};

#[derive(Debug, StructOpt)]
pub struct BackendOpts {
    #[structopt(long, default_value)]
    interface: String,
}

#[derive(Error, Debug)]
pub enum Error {
    #[error("unknown interface {0}")]
    UnknownInterface(String),
}

/// Creates the requested backend interface according to [`BackendOpts`].
pub fn create(args: &BackendOpts) -> Result<Box<dyn Transport>> {
    match args.interface.as_str() {
        "" => Ok(Box::new(EmptyTransport)),
        _ => Err(Error::UnknownInterface(args.interface.clone()).into()),
    }
}
