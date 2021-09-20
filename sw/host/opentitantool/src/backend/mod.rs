// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::Result;
use structopt::StructOpt;
use thiserror::Error;

use opentitanlib::transport::{EmptyTransport, Transport};
use opentitanlib::util::parse_int::ParseInt;

pub mod ultradebug;
pub mod verilator;

#[derive(Debug, StructOpt)]
pub struct BackendOpts {
    #[structopt(long, default_value, help = "Name of the debug interface")]
    interface: String,

    #[structopt(long, parse(try_from_str = u16::from_str),
                help="USB Vendor ID of the interface")]
    usb_vid: Option<u16>,
    #[structopt(long, parse(try_from_str = u16::from_str),
                help="USB Product ID of the interface")]
    usb_pid: Option<u16>,
    #[structopt(long, help = "USB serial number of the interface")]
    usb_serial: Option<String>,

    #[structopt(flatten)]
    verilator_opts: verilator::VerilatorOpts,
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
        "verilator" => verilator::create(&args.verilator_opts),
        "ultradebug" => ultradebug::create(args),
        _ => Err(Error::UnknownInterface(args.interface.clone()).into()),
    }
}
