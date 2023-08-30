// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::{anyhow, Context, Result};
use clap::Parser;
use cryptoki::session::UserType;
use log::LevelFilter;
use std::path::PathBuf;

use hsmtool::commands::{print_command, print_result, Commands, Dispatch, Format};
use hsmtool::module::{self, Module};
use hsmtool::profile::Profile;
use hsmtool::util::attribute::AttributeMap;

#[derive(Debug, Parser)]
struct Args {
    /// Logging level.
    #[arg(long, default_value = "warn")]
    logging: LevelFilter,

    /// Output format.
    #[arg(short, long, value_enum, default_value = "json")]
    format: Format,

    /// Use color in the output.
    #[arg(short, long)]
    color: Option<bool>,

    /// Filename of HSM profiles.  Relative to $XDG_CONFIG_HOME/hsmtool.
    #[arg(long, default_value = "profiles.json")]
    profiles: PathBuf,

    /// The name of an HSM profile to use.
    #[arg(long)]
    profile: Option<String>,

    /// Path to a PKCS11 shared library.
    #[arg(long, env = "HSMTOOL_MODULE")]
    module: String,

    /// HSM Token to use.
    #[arg(short, long, env = "HSMTOOL_TOKEN")]
    token: Option<String>,

    /// User type ('so' or 'user').
    #[arg(short, long, env = "HSMTOOL_USER", value_parser = module::parse_user_type)]
    user: Option<UserType>,

    /// Pin.
    #[arg(short, long, env = "HSMTOOL_PIN")]
    pin: Option<String>,

    /// Show JSON encode of the command.
    #[arg(long, default_value = "false")]
    show_json: bool,

    #[command(subcommand)]
    command: Commands,
}

fn main() -> Result<()> {
    let args = Args::parse();
    env_logger::Builder::from_default_env()
        .filter(None, args.logging)
        .init();
    let hsm = Module::initialize(&args.module).context(
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
        Some(hsm.connect(&profile.token, Some(profile.user), profile.pin.as_deref())?)
    } else if let Some(token) = &args.token {
        Some(hsm.connect(token, args.user, args.pin.as_deref())?)
    } else {
        None
    };

    let result = args.command.run(&(), &hsm, session.as_ref());
    print_result(args.format, args.color, result)
}
