// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::{Context, Result};
use clap::Parser;
use cryptoki::session::UserType;
use log::LevelFilter;

use hsmtool::commands::{print_result, Commands, Dispatch, Format};
use hsmtool::module;
use hsmtool::util::attribute::AttributeMap;

#[derive(Debug, Parser)]
struct Args {
    #[arg(long, default_value = "warn", help = "Logging level")]
    logging: LevelFilter,

    #[arg(
        short,
        long,
        value_enum,
        default_value = "json",
        help = "Output format"
    )]
    format: Format,

    #[arg(short, long, help = "Use color in the output")]
    color: Option<bool>,

    #[arg(long, env = "HSMTOOL_MODULE", help = "Path to a PKCS11 shared library")]
    module: String,

    #[arg(short, long, env = "HSMTOOL_TOKEN", help = "HSM Token to use")]
    token: Option<String>,

    #[arg(
        short,
        long,
        env = "HSMTOOL_USER",
        value_parser = module::parse_user_type,
        help="User type ('so' or 'user')"
    )]
    user: Option<UserType>,

    #[arg(short, long, env = "HSMTOOL_PIN", help = "Pin")]
    pin: Option<String>,

    #[command(subcommand)]
    command: Commands,
}

fn main() -> Result<()> {
    let args = Args::parse();
    env_logger::Builder::from_default_env()
        .filter(None, args.logging)
        .init();
    let pkcs11 = module::initialize(&args.module).context(
        "Loading the PKCS11 module usually depends on several environent variables.  Check HSMTOOL_MODULE, SOFTHSM2_CONF or your HSM's documentation.")?;

    // Initialize the list of all valid attribute types early.  Disable logging
    // so we don't have to see all the harmless conversion errors for the types
    // that cryptoki doesn't support.
    log::set_max_level(LevelFilter::Off);
    let _ = AttributeMap::all();
    log::set_max_level(args.logging);

    let session = if let Some(token) = &args.token {
        Some(module::connect(
            &pkcs11,
            token,
            args.user,
            args.pin.as_deref(),
        )?)
    } else {
        None
    };

    let result = args.command.run(&(), &pkcs11, session.as_ref());
    print_result(args.format, args.color, result)
}
