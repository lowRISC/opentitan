// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::Result;
use clap::Args;

use opentitanlib_core::transport::Transport;
use opentitanlib_transports::proxy::Proxy;

#[derive(Debug, Args)]
pub struct ProxyOpts {
    #[arg(long)]
    pub proxy: Option<String>,
    #[arg(long, default_value = "9900")]
    pub port: u16,
}

pub fn create(args: &ProxyOpts) -> Result<Box<dyn Transport>> {
    Ok(Box::new(Proxy::open(args.proxy.as_deref(), args.port)?))
}
