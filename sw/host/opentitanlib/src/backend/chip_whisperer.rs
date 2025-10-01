// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::Result;
use clap::Args;

use super::{Backend, BackendOpts, define_interface};
use crate::transport::Transport;
use crate::transport::chip_whisperer::ChipWhisperer;
use crate::transport::chip_whisperer::board::{Board, Cw310, Cw340};

#[derive(Debug, Args)]
pub struct ChipWhispererOpts {
    /// Comma-separated list of Chip Whisperer board UARTs for non-udev environments. List the console uart first.
    #[arg(long, alias = "cw310-uarts")]
    pub uarts: Option<String>,
}

struct ChipWhispererBackend<B>(B);

impl<B: Board + 'static> Backend for ChipWhispererBackend<B> {
    type Opts = ChipWhispererOpts;

    fn create_transport(
        args: &BackendOpts,
        cw_args: &ChipWhispererOpts,
    ) -> Result<Box<dyn Transport>> {
        let uarts = cw_args
            .uarts
            .as_ref()
            .map(|v| v.split(',').collect::<Vec<&str>>())
            .unwrap_or_default();

        Ok(Box::new(ChipWhisperer::<B>::new(
            args.usb_vid,
            args.usb_pid,
            args.usb_serial.as_deref(),
            &uarts,
        )?))
    }
}

define_interface!(
    "cw310",
    ChipWhispererBackend<Cw310>,
    "/__builtin__/opentitan_cw310.json5"
);
define_interface!(
    "cw340",
    ChipWhispererBackend<Cw340>,
    "/__builtin__/opentitan_cw340.json5"
);
