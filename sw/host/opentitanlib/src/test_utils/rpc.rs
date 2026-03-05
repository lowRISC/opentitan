// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
use anyhow::Result;
use crc::{CRC_32_ISO_HDLC, Crc};
use serde::Serialize;
use serde::de::DeserializeOwned;
use std::time::Duration;

use crate::io::console::ext::{PassFail, PassFailResult};
use crate::io::console::{ConsoleDevice, ConsoleError, ConsoleExt};
use crate::regex;
use crate::test_utils::status::Status;

// Bring in the auto-generated sources.
include!(env!("ottf"));

pub trait ConsoleSend<T>
where
    T: ConsoleDevice + ?Sized,
{
    fn send(&self, device: &T) -> Result<String>;
    fn send_with_crc(&self, device: &T) -> Result<String>;
}

impl<T, U> ConsoleSend<T> for U
where
    T: ConsoleDevice + ?Sized,
    U: Serialize,
{
    fn send(&self, device: &T) -> Result<String> {
        let s = serde_json::to_string(self)?;
        log::info!("Sending: {}", s);
        device.write(s.as_bytes())?;
        Ok(s)
    }

    fn send_with_crc(&self, device: &T) -> Result<String> {
        let s = serde_json::to_string(self)?;
        log::info!("Sending: {}", s);
        device.write(s.as_bytes())?;
        let actual_crc = OttfCrc {
            crc: Crc::<u32>::new(&CRC_32_ISO_HDLC).checksum(s.as_bytes()),
        };
        let crc_s = actual_crc.send(device)?;
        Ok(s + &crc_s)
    }
}

pub trait ConsoleRecv<T>
where
    T: ConsoleDevice + ?Sized,
{
    fn recv(device: &T, timeout: Duration, quiet: bool, skip_crc: bool) -> Result<Self>
    where
        Self: Sized;
}

impl<T, U> ConsoleRecv<T> for U
where
    T: ConsoleDevice + ?Sized,
    U: DeserializeOwned,
{
    fn recv(device: &T, timeout: Duration, quiet: bool, skip_crc: bool) -> Result<Self>
    where
        Self: Sized,
    {
        let device = device.coverage();
        let device: &dyn ConsoleDevice = if quiet { &device } else { &device.logged() };
        let result = device.wait_for_line(
            PassFail(
                regex!(r"RESP_OK:(.*) CRC:([0-9]+)"),
                regex!(r"RESP_ERR:(.*) CRC:([0-9]+)"),
            ),
            timeout,
        )?;
        println!();
        match result {
            PassFailResult::Pass(cap) => {
                let json_str = &cap[1];
                let crc_str = &cap[2];
                if !skip_crc {
                    check_crc(json_str, crc_str)?;
                }
                Ok(serde_json::from_str::<Self>(json_str)?)
            }
            PassFailResult::Fail(cap) => {
                let json_str = &cap[1];
                let crc_str = &cap[2];
                check_crc(json_str, crc_str)?;
                Err(serde_json::from_str::<Status>(json_str)?)?
            }
        }
    }
}

fn check_crc(json_str: &str, crc_str: &str) -> Result<()> {
    let crc = crc_str.parse::<u32>()?;
    let actual_crc = Crc::<u32>::new(&CRC_32_ISO_HDLC).checksum(json_str.as_bytes());
    if crc != actual_crc {
        return Err(
            ConsoleError::GenericError("CRC didn't match received json body.".into()).into(),
        );
    }
    Ok(())
}
