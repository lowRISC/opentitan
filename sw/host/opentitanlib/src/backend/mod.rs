// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::Result;
use clap::Args;
use std::path::{Path, PathBuf};
use thiserror::Error;

use crate::app::config::process_config_file;
use crate::app::{TransportWrapper, TransportWrapperBuilder};
use crate::transport::chip_whisperer::board::{Cw310, Cw340};
use crate::transport::dediprog::Dediprog;
use crate::transport::hyperdebug::{
    C2d2Flavor, ChipWhispererFlavor, ServoMicroFlavor, StandardFlavor, Ti50Flavor,
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

    /// Whether to disable DFT with a strapping config during reset. Only required in TestUnlocked*
    /// LC states activate the JTAG RV TAP. This is required since the DFT straps share the console
    /// UART pins, that hyperdebug tries to pull high. In mission mode states this should be set to
    /// false, as DFT straps are not sampled here.
    #[arg(long)]
    pub disable_dft_on_reset: bool,

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

    /// Path to OpenOCD JTAG adapter config file to use (usually Olimex, but could be another
    /// adapter).  If unspecified, will use native support of the backend transport.  (Currently
    /// only the HyperDebug transport has such native JTAG support, and for any other transport,
    /// this argument must be specified if using JTAG.)
    #[arg(long)]
    pub openocd_adapter_config: Option<PathBuf>,
}

#[derive(Error, Debug)]
pub enum Error {
    #[error("Unknown interface {0}")]
    UnknownInterface(String),
}

/// Creates the requested backend interface according to [`BackendOpts`].
pub fn create(args: &BackendOpts) -> Result<TransportWrapper> {
    let interface = args.interface.as_str();
    let mut env = TransportWrapperBuilder::new(interface.to_string(), args.disable_dft_on_reset);

    for conf_file in &args.conf {
        process_config_file(&mut env, conf_file.as_ref())?
    }
    let (backend, default_conf) = match env.get_interface() {
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
        "hyper310" => (
            hyperdebug::create::<ChipWhispererFlavor<Cw310>>(args)?,
            Some(Path::new("/__builtin__/hyperdebug_cw310.json")),
        ),
        "teacup" => (
            hyperdebug::create::<StandardFlavor>(args)?,
            Some(Path::new("/__builtin__/hyperdebug_teacup_default.json")),
        ),
        "hyper340" => (
            hyperdebug::create::<ChipWhispererFlavor<Cw340>>(args)?,
            Some(Path::new("/__builtin__/hyperdebug_cw340.json")),
        ),
        "hyperdebug" => (hyperdebug::create::<StandardFlavor>(args)?, None),
        "hyperdebug_dfu" => (hyperdebug::create_dfu(args)?, None),
        "c2d2" => (
            hyperdebug::create::<C2d2Flavor>(args)?,
            Some(Path::new("/__builtin__/h1dx_devboard_c2d2.json")),
        ),
        "servo_micro" => (
            hyperdebug::create::<ServoMicroFlavor>(args)?,
            Some(Path::new("/__builtin__/servo_micro.json")),
        ),
        "ti50" => (hyperdebug::create::<Ti50Flavor>(args)?, None),
        "cw310" => (
            chip_whisperer::create::<Cw310>(args)?,
            Some(Path::new("/__builtin__/opentitan_cw310.json")),
        ),
        "cw340" => (
            chip_whisperer::create::<Cw340>(args)?,
            Some(Path::new("/__builtin__/opentitan_cw340.json")),
        ),
        "dediprog" => {
            let dediprog: Box<dyn Transport> = Box::new(Dediprog::new(
                args.usb_vid,
                args.usb_pid,
                args.usb_serial.as_deref(),
            )?);
            (dediprog, Some(Path::new("/__builtin__/dediprog.json")))
        }
        _ => return Err(Error::UnknownInterface(interface.to_string()).into()),
    };
    if args.conf.is_empty() {
        if let Some(conf_file) = default_conf {
            process_config_file(&mut env, conf_file)?
        }
    }
    env.set_openocd_adapter_config(&args.openocd_adapter_config);
    env.build(backend)
}

pub fn create_empty_transport() -> Result<Box<dyn Transport>> {
    Ok(Box::new(EmptyTransport))
}
