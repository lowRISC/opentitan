// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use crate::interface::serve_command;
use log::LevelFilter;
use mio::{Events, Interest, Poll, Token};
use opentitanlib::backend;
use opentitanlib::io::i2c::I2cParams;
use opentitanlib::io::spi::SpiParams;
use opentitanlib::tpm::{Driver, I2cDriver, SpiDriver};
use opentitanlib::util::parse_int::ParseInt;
use std::net::{SocketAddr, TcpListener};
use structopt::StructOpt;

mod interface;

#[derive(Debug, StructOpt)]
pub enum TpmBus {
    Spi {
        #[structopt(flatten)]
        params: SpiParams,
    },
    I2C {
        #[structopt(flatten)]
        params: I2cParams,
        #[structopt(
            short,
            long,
            help = "7 bit I2C device address.",
            parse(try_from_str = ParseInt::from_str)
        )]
        address: u8,
    },
}

#[derive(Debug, StructOpt)]
#[structopt(
    name = "tpm2-test-server",
    about = "A tool for processing TPM commands over a TCP port."
)]
struct Opts {
    #[structopt(subcommand)]
    bus: TpmBus,

    #[structopt(long, default_value = "off")]
    logging: LevelFilter,

    #[structopt(flatten)]
    backend_opts: backend::BackendOpts,

    #[structopt(
        short,
        long,
        default_value = "9883",
        help = "TCP port for incoming connections."
    )]
    tpm_port: u16,
}

const CMD_TOKEN: Token = Token(0);
const PLATFORM_TOKEN: Token = Token(1);

pub fn main() -> std::io::Result<()> {
    let options = Opts::from_args();
    env_logger::Builder::from_default_env()
        .filter(None, options.logging)
        .init();
    let cmd_addr = SocketAddr::from(([127, 0, 0, 1], options.tpm_port));
    let platform_addr = SocketAddr::from(([127, 0, 0, 1], options.tpm_port + 1));
    let cmd_listener = TcpListener::bind(cmd_addr)?;
    let platform_listener = TcpListener::bind(platform_addr)?;

    let mut cmd_stream = mio::net::TcpStream::from_std(cmd_listener.accept()?.0);
    let mut platform_stream = mio::net::TcpStream::from_std(platform_listener.accept()?.0);

    let mut poll = Poll::new()?;
    let mut events = Events::with_capacity(128);
    poll.registry()
        .register(&mut platform_stream, PLATFORM_TOKEN, Interest::READABLE)?;

    poll.registry()
        .register(&mut cmd_stream, CMD_TOKEN, Interest::READABLE)?;

    let transport = backend::create(&options.backend_opts).unwrap();
    let bus: Box<dyn Driver> = match options.bus {
        TpmBus::Spi { params } => {
            let spi = params.create(&transport, "").unwrap();
            Box::new(SpiDriver::new(spi))
        }
        TpmBus::I2C { params, address } => {
            let i2c = params.create(&transport).unwrap();
            Box::new(I2cDriver::new(i2c, address))
        }
    };
    bus.init().unwrap();

    loop {
        poll.poll(&mut events, None)?;

        for event in events.iter() {
            match event.token() {
                CMD_TOKEN => {
                    if serve_command(&mut cmd_stream, &*bus).unwrap() {
                        return Ok(());
                    }
                }
                PLATFORM_TOKEN => {
                    if serve_command(&mut platform_stream, &*bus).unwrap() {
                        return Ok(());
                    }
                }
                Token(_) => todo!(),
            }
        }
    }
}
