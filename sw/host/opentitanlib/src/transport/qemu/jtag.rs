// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use std::path::PathBuf;

use crate::debug::openocd::{OpenOcd, OpenOcdJtagChain};
use crate::io::jtag::{Jtag, JtagChain, JtagParams, JtagTap};

/// Proxy between the two available JTAG TAPs in QEMU.
///
/// The QEMU model of OpenTitan does not currently implement the single multiplexed
/// JTAG socket that hardware has, instead both sockets are always visible. We defer
/// connecting OpenOCD to the socket until we know which TAP we're connecting to.
pub struct QemuJtag {
    /// Params to be forwarded to [`OpenOcdJtagChain`]
    params: JtagParams,

    /// Remote bitbang socket for the debug module.
    rv_dm_sock: PathBuf,

    /// Remote bitbang socket for the lifecycle controller.
    lc_ctrl_sock: PathBuf,
}

impl QemuJtag {
    pub fn new(params: JtagParams, rv_dm_sock: PathBuf, lc_ctrl_sock: PathBuf) -> QemuJtag {
        QemuJtag {
            params,
            rv_dm_sock,
            lc_ctrl_sock,
        }
    }
}

impl JtagChain for QemuJtag {
    fn connect(self: Box<Self>, tap: JtagTap) -> anyhow::Result<Box<dyn Jtag>> {
        let sock = match tap {
            JtagTap::RiscvTap => self.rv_dm_sock,
            JtagTap::LcTap => self.lc_ctrl_sock,
        };

        let openocd = OpenOcdJtagChain::new(
            &format!(
                "adapter driver remote_bitbang; remote_bitbang port 0; remote_bitbang host {sock}",
                sock = sock.display(),
            ),
            &self.params,
        )?;

        Box::new(openocd).connect(tap)
    }

    fn into_raw(self: Box<Self>) -> anyhow::Result<OpenOcd> {
        // We can't spawn OpenOCD until we know which TAP/socket to connect to, so we can't implement
        // this yet. Eventually QEMU should mux the TAPs through one socket to resolve this.
        todo!("QEMU JTAG does not currently support direct OpenOCD access before connection");
    }
}
