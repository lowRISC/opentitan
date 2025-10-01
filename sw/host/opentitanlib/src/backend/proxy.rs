// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::Result;
use clap::Args;

use super::{Backend, BackendOpts, define_interface};
use crate::transport::Transport;
use crate::transport::proxy::Proxy;

#[derive(Debug, Args)]
pub struct ProxyOpts {
    #[arg(long)]
    proxy: Option<String>,
    #[arg(long, default_value = "9900")]
    port: u16,
}

struct ProxyBackend;

impl Backend for ProxyBackend {
    type Opts = ProxyOpts;

    fn create_transport(_: &BackendOpts, args: &ProxyOpts) -> Result<Box<dyn Transport>> {
        Ok(Box::new(Proxy::open(args.proxy.as_deref(), args.port)?))
    }
}

define_interface!("proxy", ProxyBackend);
