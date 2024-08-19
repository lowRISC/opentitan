// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
use anyhow::{anyhow, Result};
use crc::{Crc, CRC_32_ISO_HDLC};
use regex::Regex;
use serde::de::DeserializeOwned;
use serde::Serialize;
use std::io::Write;
use std::time::Duration;

use crate::io::console::{ConsoleDevice, ConsoleError};
use crate::test_utils::status::Status;
use crate::uart::console::{ExitStatus, UartConsole};

// Bring in the auto-generated sources.
include!(env!("ottf"));

pub trait UartSend<T>
where
    T: ConsoleDevice + ?Sized,
{
    fn send(&self, device: &T) -> Result<()>;
    fn send_with_crc(&self, device: &T) -> Result<()>;
}

impl<T, U> UartSend<T> for U
where
    T: ConsoleDevice + ?Sized,
    U: Serialize,
{
    fn send(&self, device: &T) -> Result<()> {
        let s = serde_json::to_string(self)?;
        log::info!("Sending: {}", s);
        device.console_write(s.as_bytes())?;
        Ok(())
    }

    fn send_with_crc(&self, device: &T) -> Result<()> {
        let s = serde_json::to_string(self)?;
        log::info!("Sending: {}", s);
        device.console_write(s.as_bytes())?;
        let actual_crc = OttfCrc {
            crc: Crc::<u32>::new(&CRC_32_ISO_HDLC).checksum(s.as_bytes()),
        };
        actual_crc.send(device)
    }
}

pub trait UartRecv<T>
where
    T: ConsoleDevice + ?Sized,
{
    fn recv(device: &T, timeout: Duration, quiet: bool) -> Result<Self>
    where
        Self: Sized;
}

impl<T, U> UartRecv<T> for U
where
    T: ConsoleDevice + ?Sized,
    U: DeserializeOwned,
{
    fn recv(device: &T, timeout: Duration, quiet: bool) -> Result<Self>
    where
        Self: Sized,
    {
        let mut console = UartConsole {
            timeout: Some(timeout),
            timestamp: true,
            newline: true,
            exit_success: Some(Regex::new(r"RESP_OK:(.*) CRC:([0-9]+)\n")?),
            exit_failure: Some(Regex::new(r"RESP_ERR:(.*) CRC:([0-9]+)\n")?),
            ..Default::default()
        };
        let mut stdout = std::io::stdout();
        let out = if !quiet {
            let w: &mut dyn Write = &mut stdout;
            Some(w)
        } else {
            None
        };
        let result = console.interact(device, None, out)?;
        println!();
        match result {
            ExitStatus::ExitSuccess => {
                let cap = console
                    .captures(ExitStatus::ExitSuccess)
                    .expect("RESP_OK capture");
                let json_str = cap.get(1).expect("RESP_OK group").as_str();
                let crc_str = cap.get(2).expect("CRC group").as_str();
                check_crc(json_str, crc_str)?;
                Ok(serde_json::from_str::<Self>(json_str)?)
            }
            ExitStatus::ExitFailure => {
                let cap = console
                    .captures(ExitStatus::ExitFailure)
                    .expect("RESP_ERR capture");
                let json_str = cap.get(1).expect("RESP_OK group").as_str();
                let crc_str = cap.get(2).expect("CRC group").as_str();
                check_crc(json_str, crc_str)?;
                let err = serde_json::from_str::<Status>(json_str)?;
                Err(err.into())
            }
            ExitStatus::Timeout => Err(ConsoleError::GenericError("Timed Out".into()).into()),
            _ => Err(anyhow!("Impossible result: {:?}", result)),
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
