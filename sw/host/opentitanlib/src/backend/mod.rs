// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::Result;
use std::path::{Path, PathBuf};
use structopt::StructOpt;
use thiserror::Error;

use crate::app::config::process_config_file;
use crate::app::TransportWrapper;
use crate::transport::hyperdebug::c2d2::C2d2Flavor;
use crate::transport::hyperdebug::StandardFlavor;
use crate::transport::{EmptyTransport, Transport};
use crate::util::parse_int::ParseInt;

mod cw310;
mod hyperdebug;
mod proxy;
mod ti50emulator;
mod ultradebug;
mod verilator;

#[derive(Debug, StructOpt)]
pub struct BackendOpts {
    #[structopt(long, default_value = "", help = "Name of the debug interface")]
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
    cw310_opts: cw310::Cw310Opts,

    #[structopt(flatten)]
    verilator_opts: verilator::VerilatorOpts,

    #[structopt(flatten)]
    proxy_opts: proxy::ProxyOpts,

    #[structopt(flatten)]
    ti50emulator_opts: ti50emulator::Ti50EmulatorOpts,

    #[structopt(long, help = "Configuration files")]
    conf: Option<PathBuf>,
}

#[derive(Error, Debug)]
pub enum Error {
    #[error("Unknown interface {0}")]
    UnknownInterface(String),
}

/// Creates the requested backend interface according to [`BackendOpts`].
pub fn create(args: &BackendOpts) -> Result<TransportWrapper> {
    let interface = args.interface.as_str();
    let (backend, conf) = match interface {
        "" => (create_empty_transport()?, None),
        "proxy" => (proxy::create(&args.proxy_opts)?, None),
        "verilator" => (
            verilator::create(&args.verilator_opts)?,
            Some(Path::new("/__builtin__/opentitan_verilator.json")),
        ),
        "ti50emulator" => (
            ti50emulator::create(&args.ti50emulator_opts)?,
            Some(Path::new("/__builtin__/ti50emulator.json")),
        ),
        "ultradebug" => (
            ultradebug::create(args)?,
            Some(Path::new("/__builtin__/opentitan_ultradebug.json")),
        ),
        "hyperdebug" => (
            hyperdebug::create::<StandardFlavor>(args)?,
            Some(Path::new("/__builtin__/hyperdebug_cw310.json")),
        ),
        "c2d2" => (
            hyperdebug::create::<C2d2Flavor>(args)?,
            Some(Path::new("/__builtin__/h1dx_devboard.json")),
        ),
        "cw310" => (
            cw310::create(args)?,
            Some(Path::new("/__builtin__/opentitan_cw310.json")),
        ),
        _ => return Err(Error::UnknownInterface(interface.to_string()).into()),
    };
    let mut env = TransportWrapper::new(backend);

    for conf_file in args.conf.as_ref().map(PathBuf::as_ref).or(conf) {
        process_config_file(&mut env, conf_file)?
    }
    Ok(env)
}

pub fn create_empty_transport() -> Result<Box<dyn Transport>> {
    Ok(Box::new(EmptyTransport))
}
