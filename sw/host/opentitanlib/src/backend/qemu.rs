// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use std::path::PathBuf;

use anyhow::Result;
use clap::Args;

use crate::transport::Transport;
use crate::transport::qemu::Qemu;

#[derive(Clone, Debug, Args)]
pub struct QemuOpts {
    /// Path to the socket connected to the QEMU monitor.
    ///
    /// Must be configured in `control`/QMP mode (the JSON protocol).
    #[arg(long, required_if_eq("interface", "qemu"))]
    pub qemu_monitor_socket: Option<PathBuf>,

    /// Quit QEMU when finished.
    #[arg(long, default_value_t = false)]
    pub qemu_quit: bool,
}

pub fn create(args: &QemuOpts) -> Result<Box<dyn Transport>> {
    Ok(Box::new(Qemu::from_options(args.clone())?))
}
