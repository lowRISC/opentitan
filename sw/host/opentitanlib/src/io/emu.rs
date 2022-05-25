// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use crate::impl_serializable_error;
use anyhow::Result;
use serde::{Deserialize, Serialize};
use std::collections::HashMap;
use std::fmt;
use std::path::PathBuf;
use thiserror::Error;

/// Error related to the `Emulator` trait.
#[derive(Error, Debug, Serialize, Deserialize)]
pub enum EmuError {
    #[error("Invalid argument name: {0}")]
    InvalidArgumetName(String),
    #[error("Argument name: {0} has invalid value: {1}")]
    InvalidArgumentValue(String, String),
    #[error("Start failed with cause: {0}")]
    StartFailureCause(String),
    #[error("Stop failed with cause: {0}")]
    StopFailureCause(String),
    #[error("Can't restore resource to initial state: {0}")]
    ResetError(String),
    #[error("Runtime error: {0}")]
    RuntimeError(String),
}
impl_serializable_error!(EmuError);

#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum EmuValue {
    Empty,
    String(String),
    FilePath(PathBuf),
    StringList(Vec<String>),
    FilePathList(Vec<PathBuf>),
}

impl From<String> for EmuValue {
    fn from(s: String) -> Self {
        EmuValue::String(s)
    }
}

impl From<Vec<String>> for EmuValue {
    fn from(str_array: Vec<String>) -> Self {
        EmuValue::StringList(str_array)
    }
}

impl From<PathBuf> for EmuValue {
    fn from(p: PathBuf) -> Self {
        EmuValue::FilePath(p)
    }
}

impl From<Vec<PathBuf>> for EmuValue {
    fn from(path_array: Vec<PathBuf>) -> Self {
        EmuValue::FilePathList(path_array)
    }
}

#[derive(PartialEq, Eq, Clone, Copy, Debug, Serialize, Deserialize)]
pub enum EmuState {
    Off,
    On,
    Busy,
    Error,
}

impl fmt::Display for EmuState {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            EmuState::Off => write!(f, "Off"),
            EmuState::On => write!(f, "On"),
            EmuState::Busy => write!(f, "Busy"),
            EmuState::Error => write!(f, "Error"),
        }
    }
}

/// A trait which represents a `Emulator` instance
pub trait Emulator {
    /// Simple function with return `EmuState` representing current state of Emulator instance.
    fn get_state(&self) -> Result<EmuState>;

    /// Start Emulator with provided arguments.
    /// Parameter `factory_reset` is a flag that describe if internal state
    /// and "resources" should be set to its "initial state" before applying
    /// the changes from the parameter `args`.
    /// If `factory_reset` is set to true - all internal state and "resources"
    /// will be set to its "initial state". The "initial state" for most devices
    /// means that the content is set to zero.
    /// If `factory_reset` is set to false - all internal state will be preserved
    /// form last run.
    /// Parameter `args` describe set of named flags, value and resources passed
    /// to Emulator in order to update the content of its internal state.
    /// In the context of the function below, "resources" denote files
    /// representing the state of devices, for example: EEPROM, FUSES, FLASH, SRAM...
    /// (most often binary files). Resources files sent via parameter `args`
    /// cannot be modified by the Emulator directly, the Emulator backend should have
    /// copy-on-write implementations to enable resource modification during DUT Emulation.
    /// It should be noted that the method of resources interpretation
    /// and their format depends on the backend implementing the Emulator trait.
    /// More detail about supported `args` value and its content can be found
    /// in the documentation of individual backend.
    fn start(&self, factory_reset: bool, args: &HashMap<String, EmuValue>) -> Result<()>;

    /// Stop emulator instance.
    fn stop(&self) -> Result<()>;
}
