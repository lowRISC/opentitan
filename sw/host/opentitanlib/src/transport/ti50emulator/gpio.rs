// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
use std::cell::{Cell, RefCell};
use std::fmt;
use std::io::{Read, Write};
use std::rc::Rc;

use anyhow::{bail, Result};
use serde::{Deserialize, Serialize};
use std::convert::TryFrom;
use std::os::unix::net::UnixStream;
use std::path::PathBuf;

use crate::io::emu::EmuState;
use crate::io::gpio::{GpioError, GpioPin, PinMode, PullMode};
use crate::transport::ti50emulator::Inner;
use crate::transport::ti50emulator::Ti50Emulator;

const GPIO_BUF_SIZE: usize = 16;

/// Enumeration representing the GPIO control commands
/// sent through the socket.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[repr(u8)]
enum GpioStreamCommand {
    SetZero = b'0',
    SetOne = b'1',
    GetState = b'%',
}

impl From<bool> for GpioStreamCommand {
    fn from(value: bool) -> GpioStreamCommand {
        match value {
            false => GpioStreamCommand::SetZero,
            true => GpioStreamCommand::SetOne,
        }
    }
}

/// Enumeration that represents GPIO status updates caused
/// by a response to a `GetState` command.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum GpioStateUpdate {
    Value(bool),
    PinMode(Option<PinMode>),
    PullMode(PullMode),
}

impl TryFrom<u8> for GpioStateUpdate {
    type Error = GpioError;
    /// A function designed to convert the bytes sent by the GPIO stream to state changes.
    fn try_from(value: u8) -> Result<Self, Self::Error> {
        match value {
            b'0' => Ok(GpioStateUpdate::Value(false)),
            b'1' => Ok(GpioStateUpdate::Value(true)),
            b'z' => Ok(GpioStateUpdate::PinMode(None)),
            b'i' => Ok(GpioStateUpdate::PinMode(Some(PinMode::Input))),
            b'o' => Ok(GpioStateUpdate::PinMode(Some(PinMode::OpenDrain))),
            b'b' => Ok(GpioStateUpdate::PinMode(None)),
            b'f' => Ok(GpioStateUpdate::PinMode(None)),
            b'x' => Ok(GpioStateUpdate::PinMode(None)),
            b'-' => Ok(GpioStateUpdate::PullMode(PullMode::None)),
            b'u' => Ok(GpioStateUpdate::PullMode(PullMode::PullUp)),
            b'd' => Ok(GpioStateUpdate::PullMode(PullMode::PullDown)),
            _ => Err(GpioError::Generic(String::from(
                "Invalid byte during decoding GPIO stream",
            ))),
        }
    }
}

/// Structure representing GPIO pin configuration state.
#[derive(Clone, Copy, Serialize, Deserialize)]
pub struct GpioConfiguration {
    pin_mode: Option<PinMode>,
    pull_mode: PullMode,
    value: bool,
}

impl GpioConfiguration {
    /// Update current GPIO configurations by applying changes
    /// encoded in `buf`.
    pub fn update(&mut self, buf: &[u8]) -> Result<()> {
        if buf.len() > 0 {
            for data in buf.iter() {
                match GpioStateUpdate::try_from(*data)? {
                    GpioStateUpdate::Value(value) => {
                        self.value = value;
                    }
                    GpioStateUpdate::PinMode(mode) => {
                        self.pin_mode = mode;
                    }
                    GpioStateUpdate::PullMode(mode) => {
                        self.pull_mode = mode;
                    }
                }
            }
            return Ok(());
        }
        bail!("GPIO configuration buffer is empty");
    }
}

impl fmt::Display for GpioConfiguration {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{:?} {} {}", self.pin_mode, self.pull_mode, self.value)
    }
}

/// Multi value logic with drive strength representations.
/// (Subset of IEEE 1164).
enum Logic {
    StrongZero,
    StrongOne,
    WeakZero,
    WeakOne,
    HiImpedance,
}

impl fmt::Display for Logic {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Logic::StrongZero => write!(f, "0"),
            Logic::StrongOne => write!(f, "1"),
            Logic::WeakZero => write!(f, "L"),
            Logic::WeakOne => write!(f, "H"),
            Logic::HiImpedance => write!(f, "Z"),
        }
    }
}

impl From<GpioConfiguration> for Logic {
    /// Convert the GPIO state stored in `state` to multi-valued logic.
    fn from(state: GpioConfiguration) -> Logic {
        match (state.pin_mode, state.pull_mode, state.value) {
            (Some(PinMode::PushPull), _, false) => Logic::StrongZero,
            (Some(PinMode::PushPull), _, true) => Logic::StrongOne,
            (Some(PinMode::OpenDrain), _, false) => Logic::StrongZero,
            (Some(PinMode::OpenDrain), PullMode::PullUp, true) => Logic::WeakOne,
            (Some(PinMode::OpenDrain), PullMode::PullDown, true) => Logic::WeakZero,
            (Some(PinMode::OpenDrain), PullMode::None, true) => Logic::HiImpedance,
            (Some(PinMode::Input), PullMode::PullUp, _) => Logic::WeakOne,
            (Some(PinMode::Input), PullMode::PullDown, _) => Logic::WeakZero,
            (Some(PinMode::Input), PullMode::None, _) => Logic::HiImpedance,
            (None, _, _) => Logic::HiImpedance,
        }
    }
}

/// The function calculates the state of the "virtual wire" that connects the "host" and DUT GPIO port.
/// If any inconsistencies are detected between the sides, it returns an error with the problem description.
/// The state on the host side is passed by `host` argument and on DUT side by `dut`.
/// Parameter `name` contain name of GPIO pin.
fn resolve_state(name: &str, host: &Logic, dut: &Logic) -> Result<bool> {
    match (host, dut) {
        (Logic::StrongOne, Logic::StrongZero) => {
            Err(
                GpioError::PinValueConflict(name.to_string(), host.to_string(), dut.to_string())
                    .into(),
            )
        }
        (Logic::StrongOne, _) => Ok(true),
        (Logic::StrongZero, Logic::StrongOne) => {
            Err(
                GpioError::PinValueConflict(name.to_string(), host.to_string(), dut.to_string())
                    .into(),
            )
        }
        (Logic::StrongZero, _) => Ok(false),
        // Note: `dut` weak drive is stronger than `host` weak drive.
        // This selection was made for compatibility with the Ti50 chip.
        (
            Logic::WeakZero | Logic::WeakOne | Logic::HiImpedance,
            Logic::StrongOne | Logic::WeakOne,
        ) => Ok(true),
        (
            Logic::WeakZero | Logic::WeakOne | Logic::HiImpedance,
            Logic::StrongZero | Logic::WeakZero,
        ) => Ok(false),
        (Logic::WeakOne, Logic::HiImpedance) => Ok(true),
        (Logic::WeakZero, Logic::HiImpedance) => Ok(false),
        (Logic::HiImpedance, Logic::HiImpedance) => {
            Err(GpioError::PinValueUndefined(name.to_string()).into())
        }
    }
}

/// Structure representing an emulated GPIO pin.
pub struct Ti50GpioPin {
    /// Handle to Ti50Emulator internal data.
    inner: Rc<RefCell<Inner>>,
    /// This socket is valid as long as SubProcess is running.
    socket: RefCell<Option<UnixStream>>,
    /// Full path to socket file.
    path: PathBuf,
    /// Last SubProcess ID.
    last_id: Cell<u64>,
    /// Current state of DUT GPIO
    dut_state: Cell<GpioConfiguration>,
    /// Current state of host GPIO
    host_state: Cell<GpioConfiguration>,
}

impl Ti50GpioPin {
    pub fn open(ti50: &Ti50Emulator, path: &str, state: &GpioConfiguration) -> Result<Self> {
        let soc_path = ti50.inner.borrow().process.get_runtime_dir().join(path);
        Ok(Self {
            inner: ti50.inner.clone(),
            socket: RefCell::new(None),
            path: soc_path,
            last_id: Cell::new(0),
            dut_state: Cell::new(*state),
            host_state: Cell::new(GpioConfiguration {
                pin_mode: None,
                pull_mode: PullMode::None,
                value: false,
            }),
        })
    }

    /// Function re-connect socket to `SubProcess` when detect
    /// that process was restarted.
    fn reconnect(&self) -> Result<()> {
        let mut socket = self.socket.borrow_mut();
        let id = self.inner.borrow_mut().process.get_id();
        if self.last_id.get() != id {
            *socket = Some(UnixStream::connect(&self.path)?);
            self.last_id.set(id);
        }
        Ok(())
    }

    /// The function updates the current state of the GPIO configuration
    /// by sending a query to the TockOS emulator process.
    fn update_dut_state(&self) -> Result<()> {
        if let Some(ref mut pin_fd) = *self.socket.borrow_mut() {
            let mut buf: [u8; GPIO_BUF_SIZE] = [0; GPIO_BUF_SIZE];
            pin_fd.write_all(&[GpioStreamCommand::GetState as u8])?;
            let len = pin_fd.read(&mut buf[..])?;
            let mut state = self.dut_state.get();
            state.update(&buf[0..len])?;
            self.dut_state.set(state);
            return Ok(());
        }
        bail!("GPIO update DUT state fail - invalid socket");
    }

    /// Write the GPIO state in DUT by sending the SetZero/SetOne command to the TockOS emulator process.
    fn write_dut_value(&self, value: bool) -> Result<()> {
        if let Some(ref mut pin_fd) = *self.socket.borrow_mut() {
            pin_fd.write_all(&[GpioStreamCommand::from(value) as u8])?;
            return Ok(());
        }
        bail!("GPIO write DUT state fail - invalid socket");
    }

    /// Function checks whether the state of the sub-process allows GPIO operations to be performed
    fn check_state(&self) -> Result<()> {
        let process = &mut self.inner.borrow_mut().process;
        process.update_status()?;
        match process.get_state() {
            EmuState::On => Ok(()),
            state => Err(GpioError::Generic(format!(
                "Operation not supported in Emulator state: {}",
                state
            ))
            .into()),
        }
    }

    /// Function validate GPIO configuration on DUT and Host side and
    /// write `value` to Emulator process by a socket.
    fn validate_and_write(&self, value: bool) -> Result<()> {
        let mut host_state = self.host_state.get();
        let mut dut_state = self.dut_state.get();
        host_state.value = value;
        match (
            self.host_state.get().pin_mode,
            self.dut_state.get().pin_mode,
        ) {
            (Some(PinMode::PushPull) | Some(PinMode::OpenDrain), None) => {
                log::warn!(
                    "GPIO write to disable pin on target device, states host:{} target:{}",
                    host_state,
                    dut_state,
                );
            }
            (Some(PinMode::PushPull) | Some(PinMode::OpenDrain), Some(PinMode::Input)) => {
                log::debug!("GPIO write host:{} target:{}", host_state, dut_state);
            }
            (_, _) => {
                bail!(GpioError::PinModeConflict(
                    self.path.display().to_string(),
                    host_state.to_string(),
                    dut_state.to_string()
                ));
            }
        }
        dut_state.value = resolve_state(
            &self.path.to_string_lossy(),
            &Logic::from(host_state),
            &Logic::from(dut_state),
        )?;
        self.write_dut_value(dut_state.value)?;
        self.dut_state.set(dut_state);
        self.host_state.set(host_state);
        Ok(())
    }

    /// Function validate GPIO configuration on DUT and Host side
    /// and then returns resolved value of GPIO pin.
    fn validate_and_read(&self) -> Result<bool> {
        let mut host_state = self.host_state.get();
        let dut_state = self.dut_state.get();
        match (host_state.pin_mode, dut_state.pin_mode) {
            (Some(PinMode::Input), None) => {
                log::warn!(
                    "GPIO read from disable pin on target device, states host:{} target:{}",
                    host_state,
                    dut_state,
                );
            }
            (Some(PinMode::Input), Some(PinMode::PushPull) | Some(PinMode::OpenDrain)) => {
                log::debug!("GPIO read host:{} target:{}", host_state, dut_state);
            }
            (_, _) => {
                bail!(GpioError::PinModeConflict(
                    self.path.display().to_string(),
                    host_state.to_string(),
                    dut_state.to_string()
                ));
            }
        }
        host_state.value = resolve_state(
            &self.path.to_string_lossy(),
            &Logic::from(host_state),
            &Logic::from(dut_state),
        )?;
        self.host_state.set(host_state);
        Ok(host_state.value)
    }
}

/// A trait which represents a single GPIO pin.
impl GpioPin for Ti50GpioPin {
    /// Reads the value of the GPIO pin.
    fn read(&self) -> Result<bool> {
        self.check_state()?;
        self.reconnect()?;
        self.update_dut_state()?;
        return self.validate_and_read();
    }

    /// Sets the value of the GPIO pin to `value`.
    fn write(&self, value: bool) -> Result<()> {
        self.check_state()?;
        self.reconnect()?;
        self.update_dut_state()?;
        return self.validate_and_write(value);
    }

    /// Sets the mode of the GPIO pin as input, output, or open drain I/O.
    fn set_mode(&self, mode: PinMode) -> Result<()> {
        let mut state = self.host_state.get();
        state.pin_mode = Some(mode);
        self.host_state.set(state);
        Ok(())
    }

    /// Sets the pull mode of the GPIO pin.
    fn set_pull_mode(&self, mode: PullMode) -> Result<()> {
        let mut state = self.host_state.get();
        state.pull_mode = mode;
        self.host_state.set(state);
        Ok(())
    }
}
