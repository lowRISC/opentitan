// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::{Context, Result};
use clap::{Args, Subcommand};
use std::any::Any;
use std::convert::From;

use opentitanlib::app::TransportWrapper;
use opentitanlib::app::command::CommandDispatch;
use opentitanlib::io::fpga_backdoor::{BackdoorParams, enter_backdoor_loader};

/// Commands for interacting with the backdoor FPGA loader.
#[derive(Debug, Subcommand, CommandDispatch)]
pub enum InternalBackdoorCommand {
    /// Enter the backdoor loader - this *requires* resetting the device.
    Enter(BackdoorEnter),
    /// Exit the backdoor loader, finishing and de-asserting reset. Irreversible until next reset.
    Exit(BackdoorExit),
    /// Display information about the available backdoor targets
    Info(BackdoorInfo),
}

#[derive(Debug, Args)]
pub struct BackdoorEnter {}

impl CommandDispatch for BackdoorEnter {
    fn run(
        &self,
        _context: &dyn Any,
        transport: &TransportWrapper,
    ) -> Result<Option<Box<dyn erased_serde::Serialize>>> {
        enter_backdoor_loader(transport)?;

        Ok(None)
    }
}

#[derive(Debug, Args)]
pub struct BackdoorExit {}

impl CommandDispatch for BackdoorExit {
    fn run(
        &self,
        context: &dyn Any,
        transport: &TransportWrapper,
    ) -> Result<Option<Box<dyn erased_serde::Serialize>>> {
        let context = context.downcast_ref::<BackdoorCommand>().unwrap();
        let backdoor = context.params.create(transport)?;
        let backdoor = backdoor.connect(false)?;
        backdoor.set_done()?;

        Ok(None)
    }
}

#[derive(Debug, Args)]
pub struct BackdoorInfo {
    /// Optional target to query. If not specified, returns info for all targets.
    pub target: Option<String>,
}

impl CommandDispatch for BackdoorInfo {
    fn run(
        &self,
        context: &dyn Any,
        transport: &TransportWrapper,
    ) -> Result<Option<Box<dyn erased_serde::Serialize>>> {
        let context = context.downcast_ref::<BackdoorCommand>().unwrap();
        let backdoor = context.params.create(transport)?;
        let backdoor = backdoor.connect(true)?;

        let info: Box<dyn erased_serde::Serialize> = match &self.target {
            Some(id_str) => {
                let target = backdoor
                    .target_by_id_str(id_str)?
                    .context(format!("FPGA target '{id_str}' not found"))?;
                Box::new(target.info)
            }
            None => Box::new(backdoor.targets().to_vec()),
        };

        Ok(Some(info))
    }
}

#[derive(Debug, Args)]
pub struct BackdoorCommand {
    #[command(flatten)]
    params: BackdoorParams,

    #[command(subcommand)]
    command: InternalBackdoorCommand,
}

impl CommandDispatch for BackdoorCommand {
    fn run(
        &self,
        _context: &dyn Any,
        transport: &TransportWrapper,
    ) -> Result<Option<Box<dyn erased_serde::Serialize>>> {
        self.command.run(self, transport)
    }
}
