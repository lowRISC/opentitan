// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::Result;
use erased_serde::Serialize;
use std::any::Any;
use std::collections::HashMap;
use std::path::PathBuf;
use structopt::StructOpt;

use opentitanlib::app::command::CommandDispatch;
use opentitanlib::app::TransportWrapper;
use opentitanlib::io::emu::{EmuState, EmuValue};
use opentitanlib::transport::Capability;

#[derive(Debug, StructOpt)]
/// Get State of Emulator instance
pub struct EmuGetState {}

#[derive(serde::Serialize)]
pub struct EmuGetStateResult {
    pub state: EmuState,
}

impl CommandDispatch for EmuGetState {
    fn run(
        &self,
        _context: &dyn Any,
        transport: &TransportWrapper,
    ) -> Result<Option<Box<dyn Serialize>>> {
        transport
            .capabilities()?
            .request(Capability::EMULATOR)
            .ok()?;
        let emulator = transport.emulator()?;
        let state = emulator.get_state()?;
        Ok(Some(Box::new(EmuGetStateResult { state })))
    }
}

#[derive(Debug, StructOpt)]
/// Start Emulator instance
pub struct EmuStart {
    #[structopt(
        long,
        help = "Reset all presistent storage (For example: flash, otp, eeprom) to factory state"
    )]
    pub factory_reset: bool,
    #[structopt(long, help = "Emulator executable file name")]
    pub emulator_exec: Option<String>,
    #[structopt(
        long,
        help = "List of application names that will be provided in flash images"
    )]
    pub apps_list: Option<Vec<String>>,
    #[structopt(
        long,
        parse(from_os_str),
        help = "List of file paths representing Flash images"
    )]
    pub flash_list: Option<Vec<PathBuf>>,
    #[structopt(
        long,
        parse(from_os_str),
        help = "Path to file representing Emulator version state"
    )]
    pub version_init_state: Option<PathBuf>,
    #[structopt(
        long,
        parse(from_os_str),
        help = "Path to file representing PMU initial state"
    )]
    pub pmu_init_state: Option<PathBuf>,
}

fn pack_args(
    args_map: &mut HashMap<String, EmuValue>,
    key: &str,
    value: &Option<impl Into<EmuValue> + Clone>,
) {
    if let Some(value) = value {
        args_map.insert(key.to_string(), value.clone().into());
    }
}

impl CommandDispatch for EmuStart {
    fn run(
        &self,
        _context: &dyn Any,
        transport: &TransportWrapper,
    ) -> Result<Option<Box<dyn Serialize>>> {
        transport
            .capabilities()?
            .request(Capability::EMULATOR)
            .ok()?;
        let emulator = transport.emulator()?;
        let mut args: HashMap<String, EmuValue> = HashMap::new();
        pack_args(&mut args, "exec", &self.emulator_exec);
        pack_args(&mut args, "app", &self.apps_list);
        pack_args(&mut args, "flash", &self.flash_list);
        pack_args(&mut args, "version_init_state", &self.version_init_state);
        pack_args(&mut args, "pmu_init_state", &self.pmu_init_state);
        emulator.start(self.factory_reset, &args)?;
        Ok(None)
    }
}

#[derive(Debug, StructOpt)]
/// Stop Emulator instance
pub struct EmuStop {}

impl CommandDispatch for EmuStop {
    fn run(
        &self,
        _context: &dyn Any,
        transport: &TransportWrapper,
    ) -> Result<Option<Box<dyn Serialize>>> {
        transport
            .capabilities()?
            .request(Capability::EMULATOR)
            .ok()?;
        let emulator = transport.emulator()?;
        emulator.stop()?;
        Ok(None)
    }
}

#[derive(Debug, StructOpt, CommandDispatch)]
/// Commands for interacting with Emulator instance
pub enum EmuCommand {
    State(EmuGetState),
    Start(EmuStart),
    Stop(EmuStop),
}
