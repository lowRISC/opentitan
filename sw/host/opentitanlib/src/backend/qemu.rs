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

    /// Paths to the Socket / PTY connected to QEMU devices.
    /// Takes arbitrary mappings in the format '<DEVICE_NAME>:<PATH>' where
    /// <DEVICE_NAME> is the corresponding QEMU CharDev ID and <PATH> is the
    /// path that should be used for that CharDev.
    ///
    /// By default, these paths are retrieved & parsed from the QEMU monitor,
    /// but if QEMU was provided a relative path and the working directory has
    /// changed then these will be incorrect. This option provides the ability
    /// to override these paths.
    #[arg(long="qemu-device-path", value_name="NAME=PATH", num_args=1..)]
    pub qemu_device_paths: Vec<String>,

    /// Quit QEMU when finished.
    #[arg(long, default_value_t = false)]
    pub qemu_quit: bool,
}

impl QemuOpts {
    /// Check for any path override in the options for a given QEMU device
    pub fn device_path(&self, device_id: &str) -> Option<PathBuf> {
        // We expect < 10 paths, so just do a linear search
        for entry in &self.qemu_device_paths {
            if let Some((device, path)) = entry.split_once('=') {
                let device = device.to_string();
                if device.trim() == device_id {
                    return Some(PathBuf::from(path.to_string().trim()));
                }
            } else {
                log::warn!("Ignoring invalid --device-path argument: {entry}");
            }
        }

        None
    }
}

pub fn create(args: &QemuOpts) -> Result<Box<dyn Transport>> {
    Ok(Box::new(Qemu::from_options(args.clone())?))
}
