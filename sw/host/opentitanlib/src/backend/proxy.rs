// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::Result;
use clap::Args;

use crate::transport::proxy::Proxy;
use crate::transport::Transport;

#[derive(Debug, Args)]
pub struct ProxyOpts {
    #[arg(long)]
    proxy: Option<String>,
    #[arg(long, default_value = "9900")]
    port: u16,
}

pub fn create(args: &ProxyOpts) -> Result<Box<dyn Transport>> {
    Ok(Box::new(Proxy::open(args.proxy.as_deref(), args.port)?))
}
