// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::Result;
use clap::Args;
use std::path::PathBuf;
use thiserror::Error;

use opentitanlib_app::config::process_config_file;
use opentitanlib_app::{TransportWrapper, TransportWrapperBuilder};
#[cfg(feature = "chip_whisperer")]
use opentitanlib_transports::chip_whisperer::board::{Cw310, Cw340};
#[cfg(feature = "dediprog")]
use opentitanlib_transports::dediprog::Dediprog;
#[cfg(feature = "ftdi")]
use opentitanlib_transports::ftdi::chip::Ft4232hq;
#[cfg(feature = "hyperdebug")]
use opentitanlib_transports::hyperdebug::{
    C2d2Flavor, ChipWhispererFlavor, ServoMicroFlavor, StandardFlavor, Ti50Flavor,
};
use opentitanlib_core::transport::{EmptyTransport, Transport};
use opentitanlib_core::util::parse_int::ParseInt;

#[cfg(feature = "chip_whisperer")]
pub mod chip_whisperer;
#[cfg(feature = "ftdi")]
mod ftdi;
#[cfg(feature = "hyperdebug")]
mod hyperdebug;
#[cfg(feature = "proxy")]
pub mod proxy;
#[cfg(feature = "qemu")]
pub mod qemu;
#[cfg(feature = "ti50emulator")]
pub mod ti50emulator;
#[cfg(feature = "ultradebug")]
mod ultradebug;
#[cfg(feature = "verilator")]
pub mod verilator;

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

    #[cfg(feature = "chip_whisperer")]
    #[command(flatten)]
    pub opts: chip_whisperer::ChipWhispererOpts,

    #[cfg(feature = "verilator")]
    #[command(flatten)]
    pub verilator_opts: verilator::VerilatorOpts,

    #[cfg(feature = "proxy")]
    #[command(flatten)]
    pub proxy_opts: proxy::ProxyOpts,

    #[cfg(feature = "ti50emulator")]
    #[command(flatten)]
    pub ti50emulator_opts: ti50emulator::Ti50EmulatorOpts,

    #[cfg(feature = "qemu")]
    #[command(flatten)]
    pub qemu_opts: Option<qemu::QemuOpts>,

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
    env.register_io_expander_factory(opentitanlib_transports::ioexpander::create);

    for conf_file in &args.conf {
        process_config_file(&mut env, conf_file.as_ref())?
    }
    let (backend, default_conf) = match env.get_interface() {
        "" => (create_empty_transport()?, None),
        #[cfg(feature = "proxy")]
        "proxy" => (proxy::create(&args.proxy_opts)?, None),
        #[cfg(feature = "verilator")]
        "verilator" => (
            verilator::create(&args.verilator_opts)?,
            Some(std::path::Path::new("/__builtin__/opentitan_verilator.json")),
        ),
        #[cfg(feature = "ti50emulator")]
        "ti50emulator" => (
            ti50emulator::create(&args.ti50emulator_opts)?,
            Some(std::path::Path::new("/__builtin__/ti50emulator.json")),
        ),
        #[cfg(feature = "ultradebug")]
        "ultradebug" => (
            ultradebug::create(args)?,
            Some(std::path::Path::new("/__builtin__/opentitan_ultradebug.json")),
        ),
        #[cfg(all(feature = "hyperdebug", feature = "chip_whisperer"))]
        "hyper310" => (
            hyperdebug::create::<ChipWhispererFlavor<Cw310>>(args)?,
            Some(std::path::Path::new("/__builtin__/hyperdebug_cw310.json")),
        ),
        #[cfg(feature = "hyperdebug")]
        "teacup" => (
            hyperdebug::create::<StandardFlavor>(args)?,
            Some(std::path::Path::new("/__builtin__/hyperdebug_teacup_default.json")),
        ),
        #[cfg(feature = "hyperdebug")]
        "teacup-bga69" => (
            hyperdebug::create::<StandardFlavor>(args)?,
            Some(std::path::Path::new("/__builtin__/hyperdebug_teacup_bga69.json")),
        ),
        #[cfg(all(feature = "hyperdebug", feature = "chip_whisperer"))]
        "hyper340" => (
            hyperdebug::create::<ChipWhispererFlavor<Cw340>>(args)?,
            Some(std::path::Path::new("/__builtin__/hyperdebug_cw340.json")),
        ),
        #[cfg(feature = "hyperdebug")]
        "hyperdebug" => (hyperdebug::create::<StandardFlavor>(args)?, None),
        #[cfg(feature = "hyperdebug")]
        "hyperdebug_dfu" => (hyperdebug::create_dfu(args)?, None),
        #[cfg(feature = "hyperdebug")]
        "c2d2" => (
            hyperdebug::create::<C2d2Flavor>(args)?,
            Some(std::path::Path::new("/__builtin__/h1dx_devboard_c2d2.json")),
        ),
        #[cfg(feature = "hyperdebug")]
        "servo_micro" => (
            hyperdebug::create::<ServoMicroFlavor>(args)?,
            Some(std::path::Path::new("/__builtin__/servo_micro.json")),
        ),
        #[cfg(feature = "hyperdebug")]
        "ti50" => (hyperdebug::create::<Ti50Flavor>(args)?, None),
        #[cfg(feature = "chip_whisperer")]
        "cw310" => (
            chip_whisperer::create::<Cw310>(args)?,
            Some(std::path::Path::new("/__builtin__/opentitan_cw310.json")),
        ),
        #[cfg(feature = "chip_whisperer")]
        "cw340" => (
            chip_whisperer::create::<Cw340>(args)?,
            Some(std::path::Path::new("/__builtin__/opentitan_cw340.json")),
        ),
        #[cfg(feature = "ftdi")]
        "ftdi" => (
            ftdi::create::<Ft4232hq>(args)?,
            Some(std::path::Path::new("/__builtin__/opentitan_ftdi_voyager.json")),
        ),
        #[cfg(feature = "dediprog")]
        "dediprog" => {
            let dediprog: Box<dyn Transport> = Box::new(Dediprog::new(
                args.usb_vid,
                args.usb_pid,
                args.usb_serial.as_deref(),
            )?);
            (dediprog, Some(std::path::Path::new("/__builtin__/dediprog.json")))
        }
        #[cfg(feature = "qemu")]
        "qemu" => (
            qemu::create(args.qemu_opts.as_ref().unwrap())?,
            Some(std::path::Path::new("/__builtin__/opentitan_qemu.json")),
        ),
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
