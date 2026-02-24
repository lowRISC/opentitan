// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
use anyhow::{Result, anyhow};
use crc::{CRC_32_ISO_HDLC, Crc};
use regex::Regex;
use serde::Serialize;
use serde::de::DeserializeOwned;
use std::io::Write;
use std::time::Duration;

use crate::io::console::{ConsoleDevice, ConsoleError};
use crate::test_utils::status::Status;
use crate::uart::console::{ExitStatus, UartConsole};
use crate::uart::logging_plugin::LoggingPlugin;

// Bring in the auto-generated sources.
include!(env!("ottf"));

pub trait ConsoleSend<T>
where
    T: ConsoleDevice + ?Sized,
{
    fn send(&self, device: &T) -> Result<String>;
    fn send_with_crc(&self, device: &T) -> Result<String>;
    fn send_with_padding(&self, device: &T, max_size: usize) -> Result<String>;
    fn send_with_padding_and_crc(&self, device: &T, max_size: usize, quiet: bool)
    -> Result<String>;
}

impl<T, U> ConsoleSend<T> for U
where
    T: ConsoleDevice + ?Sized,
    U: Serialize,
{
    fn send(&self, device: &T) -> Result<String> {
        let s = serde_json::to_string(self)?;
        log::info!("Sending: {}", s);
        device.console_write(s.as_bytes())?;
        Ok(s)
    }

    fn send_with_crc(&self, device: &T) -> Result<String> {
        let s = serde_json::to_string(self)?;
        log::info!("Sending: {}", s);
        device.console_write(s.as_bytes())?;
        let actual_crc = OttfCrc {
            crc: Crc::<u32>::new(&CRC_32_ISO_HDLC).checksum(s.as_bytes()),
        };
        let crc_s = actual_crc.send(device)?;
        Ok(s + &crc_s)
    }

    fn send_with_padding(&self, device: &T, max_size: usize) -> Result<String> {
        let mut s = serde_json::to_string(self)?;
        let pad_len = max_size - s.len();
        let pad_str = ' '.to_string().repeat(pad_len);
        s.insert_str(s.len() - 1, &pad_str);
        device.console_write(s.as_bytes())?;
        Ok(s)
    }

    fn send_with_padding_and_crc(
        &self,
        device: &T,
        max_size: usize,
        quiet: bool,
    ) -> Result<String> {
        // Craft the UJSON string and pad with whitespace.
        let mut s = serde_json::to_string(self)?;
        let pad_len = max_size - s.len();
        let pad_str = ' '.to_string().repeat(pad_len);
        s.insert_str(s.len() - 1, &pad_str);
        // Craft the CRC and pad with whitespace.
        let actual_crc = OttfCrc {
            crc: Crc::<u32>::new(&CRC_32_ISO_HDLC).checksum(s.as_bytes()),
        };
        let max_crc = OttfCrc { crc: u32::MAX };
        let mut crc_s = serde_json::to_string(&actual_crc)?;
        let max_crc_s = serde_json::to_string(&max_crc)?;
        let crc_pad_str = ' '.to_string().repeat(max_crc_s.len() - crc_s.len());
        crc_s.insert_str(crc_s.len() - 1, &crc_pad_str);
        // Send bytes to the DUT.
        if !quiet {
            log::info!("Sending: {}", s.clone() + &crc_s);
        }
        device.console_write(s.as_bytes())?;
        device.console_write(crc_s.as_bytes())?;
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
        let mut console = UartConsole {
            timeout: Some(timeout),
            logging_plugin: LoggingPlugin::default().timestamp(true).quiet(quiet),
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
                if !skip_crc {
                    check_crc(json_str, crc_str)?;
                }
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
