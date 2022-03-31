// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::Result;
use std::path::{Path, PathBuf};
use structopt::StructOpt;
use thiserror::Error;

use crate::app::conf::ConfigurationFile;
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
    #[error("Loading configuration file `{0}`: {1}")]
    ConfReadError(PathBuf, anyhow::Error),
    #[error("Parsing configuration file `{0}`: {1}")]
    ConfParseError(PathBuf, anyhow::Error),
}

/// Creates the requested backend interface according to [`BackendOpts`].
pub fn create(args: &BackendOpts) -> Result<TransportWrapper> {
    let interface = args.interface.as_str();
    let mut env = TransportWrapper::new(match interface {
        "" => create_empty_transport(),
        "proxy" => proxy::create(&args.proxy_opts),
        "verilator" => verilator::create(&args.verilator_opts),
        "ti50emulator" => ti50emulator::create(&args.ti50emulator_opts),
        "ultradebug" => ultradebug::create(args),
        "hyperdebug" => hyperdebug::create::<StandardFlavor>(args),
        "c2d2" => hyperdebug::create::<C2d2Flavor>(args),
        "cw310" => cw310::create(args),
        _ => Err(Error::UnknownInterface(interface.to_string()).into()),
    }?);
    for conf_file in &args.conf {
        process_config_file(&mut env, conf_file)?
    }
    Ok(env)
}

pub fn create_empty_transport() -> Result<Box<dyn Transport>> {
    Ok(Box::new(EmptyTransport))
}

fn process_config_file(env: &mut TransportWrapper, conf_file: &Path) -> Result<()> {
    log::debug!("Reading config file {:?}", conf_file);
    let conf_data = std::fs::read_to_string(conf_file)
        .map_err(|e| Error::ConfReadError(conf_file.to_path_buf(), e.into()))?;
    let res: ConfigurationFile = serde_json::from_str(&conf_data)
        .map_err(|e| Error::ConfParseError(conf_file.to_path_buf(), e.into()))?;

    let subdir = conf_file.parent().unwrap_or_else(|| Path::new(""));
    for included_conf_file in &res.includes {
        let path = subdir.join(included_conf_file);
        process_config_file(env, &path)?
    }
    env.add_configuration_file(res)
}
