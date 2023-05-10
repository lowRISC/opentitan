// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
use anyhow::{anyhow, Result};
use regex::Regex;
use serde::de::DeserializeOwned;
use serde::Serialize;
use std::io::Write;
use std::time::Duration;

use crate::io::uart::{Uart, UartError};
use crate::test_utils::status::Status;
use crate::uart::console::{ExitStatus, UartConsole};

pub trait UartSend {
    fn send(&self, uart: &dyn Uart) -> Result<()>;
}

impl<T: Serialize> UartSend for T {
    fn send(&self, uart: &dyn Uart) -> Result<()> {
        let s = serde_json::to_string(self)?;
        log::info!("Sending: {}", s);
        uart.write(s.as_bytes())?;
        Ok(())
    }
}

pub trait UartRecv {
    fn recv(uart: &dyn Uart, timeout: Duration, quiet: bool) -> Result<Self>
    where
        Self: Sized;
}

impl<T: DeserializeOwned> UartRecv for T {
    fn recv(uart: &dyn Uart, timeout: Duration, quiet: bool) -> Result<Self>
    where
        Self: Sized,
    {
        let mut console = UartConsole {
            timeout: Some(timeout),
            timestamp: true,
            newline: true,
            exit_success: Some(Regex::new(r"RESP_OK:(.*)\r")?),
            exit_failure: Some(Regex::new(r"RESP_ERR:(.*)\r")?),
            ..Default::default()
        };
        let mut stdout = std::io::stdout();
        let out = if !quiet {
            let w: &mut dyn Write = &mut stdout;
            Some(w)
        } else {
            None
        };
        let result = console.interact(uart, None, out)?;
        println!();
        match result {
            ExitStatus::ExitSuccess => {
                let cap = console
                    .captures(ExitStatus::ExitSuccess)
                    .expect("RESP_OK capture");
                let s = cap.get(1).expect("RESP_OK group").as_str();
                Ok(serde_json::from_str::<Self>(s)?)
            }
            ExitStatus::ExitFailure => {
                let cap = console
                    .captures(ExitStatus::ExitFailure)
                    .expect("RESP_ERR capture");
                let s = cap.get(1).expect("RESP_ERR group").as_str();
                let err = serde_json::from_str::<Status>(s)?;
                Err(err.into())
            }
            ExitStatus::Timeout => Err(UartError::GenericError("Timed Out".into()).into()),
            _ => Err(anyhow!("Impossible result: {:?}", result)),
        }
    }
}
