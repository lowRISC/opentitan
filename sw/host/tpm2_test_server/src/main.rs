// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use crate::interface::serve_command;
use clap::{Parser, Subcommand};
use log::LevelFilter;
use opentitanlib::backend;
use opentitanlib::io::i2c::I2cParams;
use opentitanlib::io::spi::SpiParams;
use opentitanlib::tpm::{Driver, I2cDriver, SpiDriver};
use tokio::net::TcpListener;

mod interface;

#[derive(Debug, Subcommand)]
pub enum TpmBus {
    Spi {
        #[command(flatten)]
        params: SpiParams,

        /// Pin used for signalling by Google security chips
        #[arg(long)]
        gsc_ready: Option<String>,
    },
    I2C {
        #[command(flatten)]
        params: I2cParams,

        /// Pin used for signalling by Google security chips
        #[arg(long)]
        gsc_ready: Option<String>,
    },
}

#[derive(Debug, Parser)]
#[command(
    name = "tpm2-test-server",
    about = "A tool for processing TPM commands over a TCP port."
)]
struct Opts {
    #[command(subcommand)]
    bus: TpmBus,

    #[arg(long, default_value = "off")]
    logging: LevelFilter,

    #[command(flatten)]
    backend_opts: backend::BackendOpts,

    /// TCP port for incoming connections.
    #[arg(short, long, default_value = "9883")]
    tpm_port: u16,
}

#[tokio::main]
async fn main() -> anyhow::Result<()> {
    let options = Opts::parse();
    env_logger::Builder::from_default_env()
        .filter(None, options.logging)
        .init();
    let cmd_listener = TcpListener::bind(("127.0.0.1", options.tpm_port)).await?;
    let port = cmd_listener.local_addr()?.port();
    let platform_listener = TcpListener::bind(("127.0.0.1", port + 1)).await?;
    log::info!("Listening on ports {} and {}", port, port + 1);

    let mut cmd_stream = cmd_listener.accept().await?.0;
    let mut platform_stream = platform_listener.accept().await?.0;

    let transport = backend::create(&options.backend_opts)?;
    let bus: Box<dyn Driver> = match options.bus {
        TpmBus::Spi { params, gsc_ready } => {
            let spi = params.create(&transport, "TPM")?;
            if let Some(pin) = &gsc_ready {
                spi.set_pins(None, None, None, None, Some(&transport.gpio_pin(pin)?))?;
            }
            Box::new(SpiDriver::new(spi, gsc_ready.is_some())?)
        }
        TpmBus::I2C { params, gsc_ready } => {
            let i2c = params.create(&transport, "TPM")?;
            if let Some(pin) = &gsc_ready {
                i2c.set_pins(None, None, Some(&transport.gpio_pin(pin)?))?;
            }
            Box::new(I2cDriver::new(i2c, gsc_ready.is_some())?)
        }
    };
    bus.init()?;

    tokio::select! {
        v = serve_command(&mut cmd_stream, &*bus) => v?,
        v = serve_command(&mut platform_stream, &*bus) => v?,
    }

    Ok(())
}
