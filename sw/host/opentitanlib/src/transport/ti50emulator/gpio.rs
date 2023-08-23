// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
use std::cell::{Cell, RefCell};
use std::fmt;
use std::io::{Read, Write};
use std::rc::Rc;

use anyhow::{bail, Result};
use serde::{Deserialize, Deserializer, Serialize, Serializer};
use std::convert::TryFrom;
use std::os::unix::net::UnixStream;
use std::path::PathBuf;

use crate::io::emu::EmuState;
use crate::io::gpio::{self, GpioError, GpioPin, PinMode, PullMode};
use crate::transport::ti50emulator::Inner;

const GPIO_BUF_SIZE: usize = 16;

/// Structure representing GPIO pin configuration state.
#[derive(Clone, Copy, Serialize, Deserialize)]
pub struct GpioConfiguration {
    pin_mode: PinMode,
    pull_mode: PullMode,
    value: bool,
}

impl GpioConfiguration {
    pub fn default() -> Self {
        Self {
            pin_mode: PinMode::Input,
            pull_mode: PullMode::None,
            value: false,
        }
    }
}

/// Multi value logic with drive strength representations.
/// (Subset of IEEE 1164).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[repr(u8)]
pub enum Logic {
    StrongZero = b'0',
    StrongOne = b'1',
    WeakZero = b'L',
    WeakOne = b'H',
    HiImpedance = b'Z',
}

impl TryFrom<u8> for Logic {
    type Error = GpioError;
    fn try_from(value: u8) -> Result<Self, Self::Error> {
        match value {
            b'0' => Ok(Self::StrongZero),
            b'1' => Ok(Self::StrongOne),
            b'Z' => Ok(Self::HiImpedance),
            b'H' => Ok(Self::WeakOne),
            b'L' => Ok(Self::WeakZero),
            _ => Err(GpioError::Generic(format!(
                "Invalid byte value during decoding GPIO stream hex: {:#04x} char: '{}'",
                value, value as char
            ))),
        }
    }
}

impl fmt::Display for Logic {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", char::from(*self as u8))
    }
}

impl Serialize for Logic {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        serializer.serialize_str(&self.to_string())
    }
}

impl<'de> Deserialize<'de> for Logic {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        let val = String::deserialize(deserializer)?;
        Ok(match val.as_str() {
            "0" => Logic::StrongZero,
            "1" => Logic::StrongOne,
            "L" => Logic::WeakZero,
            "H" => Logic::WeakOne,
            "Z" => Logic::HiImpedance,
            _ => {
                return Err(serde::de::Error::custom(format!(
                    "Unrecognized logic level: {}",
                    val
                )))
            }
        })
    }
}

impl From<GpioConfiguration> for Logic {
    /// Convert the GPIO state stored in `state` to multi-valued logic.
    fn from(state: GpioConfiguration) -> Logic {
        match (state.pin_mode, state.pull_mode, state.value) {
            (PinMode::PushPull, _, false) => Logic::StrongZero,
            (PinMode::PushPull, _, true) => Logic::StrongOne,
            (PinMode::OpenDrain, _, false) => Logic::StrongZero,
            (_, PullMode::PullUp, _) => Logic::WeakOne,
            (_, PullMode::PullDown, _) => Logic::WeakZero,
            (_, PullMode::None, _) => Logic::HiImpedance,
        }
    }
}

/// The function calculates the state of the "virtual wire" that connects the "host" and DUT GPIO port.
/// If any inconsistencies are detected between the sides, it returns an error with the problem description.
/// The state on the host side is passed by `host` argument and on DUT side by `dut`.
/// Parameter `name` contain name of GPIO pin.
fn resolve_state(name: &str, host: Logic, dut: Logic) -> Result<bool> {
    match (host, dut) {
        // Host strong drive is stronger than the simulated dut, in order to simulate attackers
        // overdriving write-protect or other signals.
        (Logic::StrongOne, _) => Ok(true),
        (Logic::StrongZero, _) => Ok(false),
        (_, Logic::StrongOne) => Ok(true),
        (_, Logic::StrongZero) => Ok(false),
        // Dut weak drive is stronger than host weak drive, in order to easily simulate weak
        // strappings.
        (_, Logic::WeakOne) => Ok(true),
        (_, Logic::WeakZero) => Ok(false),
        (Logic::WeakOne, _) => Ok(true),
        (Logic::WeakZero, _) => Ok(false),
        (Logic::HiImpedance, Logic::HiImpedance) => {
            Err(GpioError::PinValueUndefined(name.to_string()).into())
        }
    }
}

/// Structure representing an emulated GPIO pin.
pub struct Ti50GpioPin {
    /// Handle to Ti50Emulator internal data.
    inner: Rc<Inner>,
    /// Canonical name of this GPIO pin
    name: String,
    /// This socket is valid as long as SubProcess is running.
    socket: RefCell<Option<UnixStream>>,
    /// Full path to socket file.
    path: PathBuf,
    /// Last SubProcess ID.
    last_id: Cell<u64>,
    /// Current state of DUT GPIO
    dut_state: Cell<Logic>,
    /// Default state of the DUT GPIO
    default_level: Logic,
}

impl Ti50GpioPin {
    pub fn open(inner: &Rc<Inner>, name: &str, state: Logic) -> Result<Self> {
        let soc_path = inner
            .process
            .borrow()
            .get_runtime_dir()
            .join(format!("gpio{}", name));
        Ok(Self {
            inner: inner.clone(),
            name: name.to_string(),
            socket: RefCell::new(None),
            path: soc_path,
            last_id: Cell::new(0),
            dut_state: Cell::new(state),
            default_level: state,
        })
    }

    const STREAM_CMD_GET_STATE: u8 = b'?';
    const STREAM_RESP_GET_STATE: u8 = b'!';

    /// Function re-connect socket to `SubProcess` when detect
    /// that process was restarted.
    fn reconnect(&self) -> Result<()> {
        let mut socket = self.socket.borrow_mut();
        let id = self.inner.process.borrow().get_id();
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
            pin_fd.write_all(&[Self::STREAM_CMD_GET_STATE])?;
            let mut seen_response = false;
            while !seen_response {
                let len = pin_fd.read(&mut buf[..])?;
                for ch in &buf[..len] {
                    if *ch == Self::STREAM_RESP_GET_STATE {
                        seen_response = true;
                    } else {
                        self.dut_state.set(Logic::try_from(*ch)?);
                    }
                }
            }
            return Ok(());
        }
        bail!("GPIO update DUT state fail - invalid socket");
    }

    /// Write how the simulated host environment drives the GPIO signal, by sending the Logic
    /// character to the TockOS emulator process.
    fn write_host_state(&self, value: Logic) -> Result<()> {
        if let Some(ref mut pin_fd) = *self.socket.borrow_mut() {
            pin_fd.write_all(&[value as u8])?;
            return Ok(());
        }
        bail!("GPIO write HOST state fail - invalid socket");
    }

    /// Function validate GPIO configuration on DUT and Host side
    /// and then returns resolved value of GPIO pin.
    fn validate_and_read(&self) -> Result<bool> {
        let mut gpio_map = self.inner.gpio_map.borrow_mut();
        let host_state = gpio_map.get_mut(&self.name).unwrap();
        let dut_state = self.dut_state.get();
        resolve_state(
            &self.path.to_string_lossy(),
            Logic::from(*host_state),
            dut_state,
        )
    }

    /// Modifies some aspect of the Host output drive, as given by the `update_fn`, and then
    /// notifies the DUT about the new state of the Host drive.
    fn update_and_notify(&self, update_fn: impl Fn(&mut GpioConfiguration)) -> Result<()> {
        let mut gpio_map = self.inner.gpio_map.borrow_mut();
        let host_state = gpio_map.get_mut(&self.name).unwrap();
        update_fn(host_state);
        if EmuState::On == self.inner.process.borrow().get_state() {
            self.reconnect()?;
            self.write_host_state(Logic::from(*host_state))?;
        }
        Ok(())
    }
}

/// A trait which represents a single GPIO pin.
impl GpioPin for Ti50GpioPin {
    /// Reads the value of the GPIO pin.
    fn read(&self) -> Result<bool> {
        if EmuState::On == self.inner.process.borrow().get_state() {
            self.reconnect()?;
            self.update_dut_state()?;
        }
        self.validate_and_read()
    }

    /// Sets the value of the GPIO pin to `value`.
    fn write(&self, value: bool) -> Result<()> {
        self.update_and_notify(|host_state| host_state.value = value)
    }

    fn reset(&self) -> Result<()> {
        // An error is never expected due to the Weak::* host.
        let state = resolve_state("Unreachable", Logic::WeakZero, self.default_level).unwrap();
        self.write(state)
    }

    /// Sets the mode of the GPIO pin as input, output, or open drain I/O.
    fn set_mode(&self, mode: gpio::PinMode) -> Result<()> {
        match mode {
            PinMode::Input | PinMode::OpenDrain | PinMode::PushPull => {
                self.update_and_notify(|host_state| host_state.pin_mode = mode)
            }
            _ => Err(GpioError::UnsupportedPinMode(mode).into()),
        }
    }

    /// Sets the pull mode of the GPIO pin.
    fn set_pull_mode(&self, mode: PullMode) -> Result<()> {
        self.update_and_notify(|host_state| host_state.pull_mode = mode)
    }
}
