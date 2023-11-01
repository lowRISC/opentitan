// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

//! Utilities for enabling or disabling external clock injection through JTAG to the clock manager.

use std::time::Duration;

use thiserror::Error;

use top_earlgrey::top_earlgrey;

use crate::chip::boolean::MultiBitBool4;
use crate::dif::clkmgr::{ClkmgrExtclkCtrl, ClkmgrReg};
use crate::io::jtag::Jtag;
use crate::test_utils::poll;

/// Available speeds for the external clock.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ClockSpeed {
    /// Approximately 1/2 of nominal frequency.
    Low,
    /// Approximately nominal frequency.
    High,
}

/// Controls for enabling or disabling external clock injection.
pub struct ExternalClock;

impl ExternalClock {
    /// Base address of the clock manager.
    const CLKMGR_BASE_ADDR: u32 = top_earlgrey::CLKMGR_AON_BASE_ADDR as u32;

    /// Addresses of clock manager registers in memory.
    const EXTCLK_CTRL_REGWEN_ADDR: u32 =
        Self::CLKMGR_BASE_ADDR + ClkmgrReg::ExtclkCtrlRegwen as u32;
    const EXTCLK_CTRL_ADDR: u32 = Self::CLKMGR_BASE_ADDR + ClkmgrReg::ExtclkCtrl as u32;
    const EXTCLK_STATUS_ADDR: u32 = Self::CLKMGR_BASE_ADDR + ClkmgrReg::ExtclkStatus as u32;

    /// Durations for polling of the STATUS register.
    const POLL_TIMEOUT: Duration = Duration::from_millis(500);
    const POLL_DELAY: Duration = Duration::from_millis(5);

    /// Enable the external clock at the given speed.
    pub fn enable(jtag: &mut dyn Jtag, speed: ClockSpeed) -> Result<(), ExternalClockError> {
        if !Self::write_enabled(jtag)? {
            return Err(ExternalClockError::WriteDisabled);
        }

        // Fields and their values for the EXTCLK_CTRL register.
        let hi_speed = match speed {
            ClockSpeed::Low => MultiBitBool4::False,
            ClockSpeed::High => MultiBitBool4::True,
        };
        let fields = [
            (ClkmgrExtclkCtrl::SEL, MultiBitBool4::True),
            (ClkmgrExtclkCtrl::HI_SPEED_SEL, hi_speed),
        ];

        // OR the fields together to get the register value.
        let extclk_ctrl = fields.into_iter().fold(0, |acc, (field, value)| {
            acc | field.emplace(u8::from(value) as u32)
        });

        // Set the EXTCLK_CTRL register.
        jtag.write_memory32(Self::EXTCLK_CTRL_ADDR, &[extclk_ctrl])
            .map_err(|source| ExternalClockError::Jtag { source })?;

        Self::wait_for_ack(jtag)?;

        Ok(())
    }

    /// Disable the external clock.
    pub fn disable(jtag: &mut dyn Jtag) -> Result<(), ExternalClockError> {
        if !Self::write_enabled(jtag)? {
            return Err(ExternalClockError::WriteDisabled);
        }

        // Set the EXTCLK_CTRL register.
        let extclk_ctrl = ClkmgrExtclkCtrl::SEL.emplace(u8::from(MultiBitBool4::False) as u32);
        jtag.write_memory32(Self::EXTCLK_CTRL_ADDR, &[extclk_ctrl])
            .map_err(|source| ExternalClockError::Jtag { source })?;

        Self::wait_for_ack(jtag)?;

        Ok(())
    }

    /// Returns the CLKMGR_EXTCLK_REGWEN setting which shows whether the
    /// `EXTCLK_CTRL` register can be written.
    fn write_enabled(jtag: &mut dyn Jtag) -> Result<bool, ExternalClockError> {
        let mut buf = [0];
        jtag.read_memory32(Self::EXTCLK_CTRL_REGWEN_ADDR, &mut buf)
            .map_err(|source| ExternalClockError::Jtag { source })?;

        Ok(buf[0] & 1 == 1)
    }

    /// Wait until the clock manager reports that the clock has changed to the external source.
    fn wait_for_ack(jtag: &mut dyn Jtag) -> Result<(), ExternalClockError> {
        poll::poll_until(Self::POLL_TIMEOUT, Self::POLL_DELAY, || {
            // Check the status register.
            let mut status_buf = [0];
            jtag.read_memory32(Self::EXTCLK_STATUS_ADDR, &mut status_buf)
                .map_err(|source| ExternalClockError::Jtag { source })?;

            Ok(status_buf[0] == u8::from(MultiBitBool4::True) as u32)
        })
        .map_err(|source| ExternalClockError::Nack { source })
    }
}

/// Failures when setting the external clock.
#[derive(Debug, Error)]
#[non_exhaustive]
pub enum ExternalClockError {
    #[error("failed to communicate over JTAG")]
    Jtag { source: anyhow::Error },

    #[error("did not read ACK for external clock change")]
    Nack { source: anyhow::Error },

    #[error("writing to external clock registers is disabled")]
    WriteDisabled,
}
