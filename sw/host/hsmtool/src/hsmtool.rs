// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::{anyhow, Context, Result};
use clap::Parser;
use cryptoki::session::UserType;
use log::LevelFilter;
use std::path::PathBuf;

use hsmtool::commands::{print_command, print_result, Commands, Dispatch, Format};
use hsmtool::module;
use hsmtool::profile::Profile;
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

    #[arg(
        long,
        default_value = "profiles.json",
        help = "Filename of HSM profiles.  Relative to $XDG_CONFIG_HOME/hsmtool."
    )]
    profiles: PathBuf,

    #[arg(long, help = "The name of an HSM profile to use")]
    profile: Option<String>,

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

    #[arg(
        long,
        default_value = "false",
        help = "Show JSON encode of the command"
    )]
    show_json: bool,

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

    if args.show_json {
        return print_command(args.format, args.color, args.command.leaf());
    }

    let session = if let Some(profile) = &args.profile {
        let profiles = Profile::load(&args.profiles)?;
        let profile = profiles
            .get(profile)
            .ok_or_else(|| anyhow!("Profile {profile:?} not found."))?;
        Some(module::connect(
            &pkcs11,
            &profile.token,
            Some(profile.user),
            profile.pin.as_deref(),
        )?)
    } else if let Some(token) = &args.token {
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
