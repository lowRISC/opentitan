// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::Result;
use clap::Args;
use std::path::{Path, PathBuf};
use std::rc::Rc;
use thiserror::Error;

use crate::app::config::process_config_file;
use crate::app::{TransportWrapper, TransportWrapperBuilder};
use crate::transport::chip_whisperer::board::{Cw310, Cw340};
use crate::transport::dediprog::Dediprog;
use crate::transport::hyperdebug::{
    C2d2Flavor, CW310Flavor, ServoMicroFlavor, StandardFlavor, Ti50Flavor,
};
use crate::transport::{EmptyTransport, Transport};
use crate::util::parse_int::ParseInt;

mod chip_whisperer;
mod hyperdebug;
mod proxy;
mod ti50emulator;
mod ultradebug;
mod verilator;

#[derive(Debug, Args)]
pub struct BackendOpts {
    /// Name of the debug interface.
    #[arg(long, default_value = "")]
    pub interface: String,

    /// USB Vendor ID of the interface.
    #[arg(long, value_parser = u16::from_str)]
    pub usb_vid: Option<u16>,
    /// USB Product ID of the interface.
    #[arg(long, value_parser = u16::from_str)]
    pub usb_pid: Option<u16>,
    /// USB serial number of the interface.
    #[arg(long)]
    pub usb_serial: Option<String>,

    #[command(flatten)]
    pub opts: chip_whisperer::ChipWhispererOpts,

    #[command(flatten)]
    pub verilator_opts: verilator::VerilatorOpts,

    #[command(flatten)]
    pub proxy_opts: proxy::ProxyOpts,

    #[command(flatten)]
    pub ti50emulator_opts: ti50emulator::Ti50EmulatorOpts,

    /// Configuration files.
    #[arg(long, num_args = 1)]
    pub conf: Vec<PathBuf>,
}

#[derive(Error, Debug)]
pub enum Error {
    #[error("Unknown interface {0}")]
    UnknownInterface(String),
}

/// Creates the requested backend interface according to [`BackendOpts`].
pub fn create(args: &BackendOpts) -> Result<TransportWrapper> {
    let interface = args.interface.as_str();
    let mut builder = TransportWrapperBuilder::new(interface.to_string());

    for conf_file in &args.conf {
        process_config_file(&mut builder, conf_file.as_ref())?
    }
    if args.conf.is_empty() {
        if let Some(conf_file) = get_config_file(interface)? {
            process_config_file(&mut builder, Path::new(conf_file))?
        }
    }
    let interface = builder.get_interface();
    let io_mapper = Rc::new(builder.build_io_mapper()?);
    let backend = build_transport(interface, args)?;
    builder.build_wrapper(backend, io_mapper)
}

fn build_transport(
    interface: &str,
    args: &BackendOpts,
) -> Result<Box<dyn crate::transport::Transport>> {
    Ok(match interface {
        "" => create_empty_transport()?,
        "proxy" => proxy::create(&args.proxy_opts)?,
        "verilator" => verilator::create(&args.verilator_opts)?,
        "ti50emulator" => ti50emulator::create(&args.ti50emulator_opts)?,
        "ultradebug" => ultradebug::create(args)?,
        "hyper310" => hyperdebug::create::<CW310Flavor>(args)?,
        "hyperdebug" => hyperdebug::create::<StandardFlavor>(args)?,
        "hyperdebug_dfu" => hyperdebug::create_dfu(args)?,
        "c2d2" => hyperdebug::create::<C2d2Flavor>(args)?,
        "servo_micro" => hyperdebug::create::<ServoMicroFlavor>(args)?,
        "ti50" => hyperdebug::create::<Ti50Flavor>(args)?,
        "cw310" => chip_whisperer::create::<Cw310>(args)?,
        "cw340" => chip_whisperer::create::<Cw340>(args)?,
        "dediprog" => Box::new(Dediprog::new(
            args.usb_vid,
            args.usb_pid,
            args.usb_serial.as_deref(),
        )?),
        _ => return Err(Error::UnknownInterface(interface.to_string()).into()),
    })
}

fn get_config_file(interface: &str) -> Result<Option<&str>> {
    Ok(Some(match interface {
        "" | "proxy" | "hyperdebug" | "hyperdebug_dfu" | "ti50" => return Ok(None),
        "verilator" => "/__builtin__/opentitan_verilator.json",
        "ti50emulator" => "/__builtin__/ti50emulator.json",
        "ultradebug" => "/__builtin__/opentitan_ultradebug.json",
        "hyper310" => "/__builtin__/hyperdebug_cw310.json",
        "c2d2" => "/__builtin__/h1dx_devboard_c2d2.json",
        "servo_micro" => "/__builtin__/servo_micro.json",
        "cw310" => "/__builtin__/opentitan_cw310.json",
        "cw340" => "/__builtin__/opentitan_cw340.json",
        "dediprog" => "/__builtin__/dediprog.json",
        _ => return Err(Error::UnknownInterface(interface.to_string()).into()),
    }))
}

pub fn create_empty_transport() -> Result<Box<dyn Transport>> {
    Ok(Box::new(EmptyTransport))
}
