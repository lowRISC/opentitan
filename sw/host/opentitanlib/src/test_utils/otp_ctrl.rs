// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

//! This module contains code for programming and reading OTP parameters
//! through the Direct Access Interface.
//!
//! Beware that OTP parameters can only be written once and can be corrupted if
//! written again.

use std::mem;
use std::time::Duration;

use anyhow::{bail, Context};
use thiserror::Error;

use top_earlgrey::top_earlgrey;

use crate::dif::otp_ctrl::{
    DaiParam, DirectAccessCmd, Granularity, OtpCtrlReg, OtpCtrlStatus, OtpParamMmap, Partition,
};
use crate::io::jtag::Jtag;
use crate::test_utils::poll;

/// Controls for reading and writing OTP parameters.
pub struct OtpParam;
impl OtpParam {
    /// Read a parameter from OTP into an output buffer.
    pub fn read_param(jtag: &dyn Jtag, param: DaiParam, out_buf: &mut [u32]) -> OtpDaiResult<()> {
        let OtpParamMmap { byte_addr, size } = param.mmap();

        if mem::size_of_val(out_buf) < size as usize {
            let err = OtpDaiError::BufSize {
                buf_size: mem::size_of_val(out_buf),
                param_size: size,
            };
            return Err(err);
        }

        let Partition { access_granule, .. } = param.partition();

        match access_granule {
            Granularity::B32 => {
                let out_iter = out_buf.iter_mut().take(size as usize);
                for (idx, out_word) in out_iter.enumerate() {
                    let addr = byte_addr + (idx * mem::size_of::<u32>()) as u32;
                    let [lower, _] = OtpDai::read(jtag, addr, access_granule)?;
                    *out_word = lower;
                }
            }
            Granularity::B64 => {
                let out_iter = out_buf.chunks_mut(2).take(size as usize / 2);
                for (idx, out_words) in out_iter.enumerate() {
                    let addr = byte_addr + (idx * mem::size_of::<u64>()) as u32;
                    let otp_words = OtpDai::read(jtag, addr, access_granule)?;
                    out_words[0] = otp_words[0];
                    out_words[1] = otp_words[1];
                }
            }
        }

        Ok(())
    }

    /// Write a value from a buffer to an OTP parameter.
    pub fn write_param(jtag: &dyn Jtag, param: DaiParam, data: &[u32]) -> OtpDaiResult<()> {
        let OtpParamMmap { byte_addr, size } = param.mmap();

        if mem::size_of_val(data) > size as usize {
            let err = OtpDaiError::BufSize {
                buf_size: mem::size_of_val(data),
                param_size: size,
            };
            return Err(err);
        }

        let Partition { access_granule, .. } = param.partition();

        match access_granule {
            Granularity::B32 => {
                let data_iter = data.iter().take(size as usize);
                for (idx, data_word) in data_iter.enumerate() {
                    let addr = byte_addr + (idx * mem::size_of::<u32>()) as u32;
                    OtpDai::write(jtag, addr, access_granule, [*data_word, 0x00])?;
                }
            }
            Granularity::B64 => {
                let data_iter = data.chunks(2).take(size as usize / 2);
                for (idx, data_words) in data_iter.enumerate() {
                    let addr = byte_addr + (idx * mem::size_of::<u64>()) as u32;
                    OtpDai::write(jtag, addr, access_granule, [data_words[0], data_words[1]])?;
                }
            }
        }

        Ok(())
    }
}

/// Commands for operating on OTP partitions.
pub struct OtpPartition;
impl OtpPartition {
    /// Lock the given partition by calculating its digest.
    pub fn lock(jtag: &dyn Jtag, partition: Partition) -> OtpDaiResult<()> {
        OtpDai::lock(jtag, partition.byte_addr)
    }

    /// Read back this partition's digest from the OTP.
    ///
    /// This goes via the DAI, but partitions are also exposed via CSRs after reset.
    pub fn read_digest(jtag: &dyn Jtag, partition: Partition) -> OtpDaiResult<[u32; 2]> {
        let OtpParamMmap { byte_addr, size } = partition.digest;
        assert_eq!(size, 8, "OTP partition digests should be 2 words in size");

        OtpDai::read(jtag, byte_addr, Granularity::B64)
    }
}

/// Direct Access Interface to the OTP.
struct OtpDai;
impl OtpDai {
    /// Base address of the OTP controller in memory.
    const OTP_CTRL_BASE_ADDR: u32 = top_earlgrey::OTP_CTRL_CORE_BASE_ADDR as u32;

    // Polling timeout and delay while waiting on statuses.
    const POLL_TIMEOUT: Duration = Duration::from_millis(500);
    const POLL_DELAY: Duration = Duration::from_millis(5);

    /// Perform a single read over the Direct Access Interface.
    ///
    /// On success, returns an array of words `[lower, upper]` where `upper` is non-zero
    /// for 64-bit granularity reads.
    pub fn read(jtag: &dyn Jtag, byte_addr: u32, granule: Granularity) -> OtpDaiResult<[u32; 2]> {
        Self::wait_for_idle(jtag)?;

        // Set the DAI address to read from.
        let dai_address_addr = Self::OTP_CTRL_BASE_ADDR + OtpCtrlReg::DirectAccessAddress as u32;
        jtag.write_memory32(dai_address_addr, &[byte_addr])
            .map_err(|source| OtpDaiError::Jtag { source })?;

        // Trigger a read command.
        let dai_cmd_addr = Self::OTP_CTRL_BASE_ADDR + OtpCtrlReg::DirectAccessCmd as u32;
        jtag.write_memory32(dai_cmd_addr, &[DirectAccessCmd::RD.bits()])
            .map_err(|source| OtpDaiError::Jtag { source })?;

        Self::wait_for_idle(jtag)?;

        let dai_rdata0_addr = Self::OTP_CTRL_BASE_ADDR + OtpCtrlReg::DirectAccessRdata0 as u32;
        let dai_rdata1_addr = Self::OTP_CTRL_BASE_ADDR + OtpCtrlReg::DirectAccessRdata1 as u32;

        let mut rdata = [0x00; 2];

        jtag.read_memory32(dai_rdata0_addr, &mut rdata[0..=0])
            .map_err(|source| OtpDaiError::Jtag { source })?;

        if granule == Granularity::B64 {
            jtag.read_memory32(dai_rdata1_addr, &mut rdata[1..=1])
                .map_err(|source| OtpDaiError::Jtag { source })?;
        }

        Ok(rdata)
    }

    /// Perform a single write over the Direct Access Interface.
    pub fn write(
        jtag: &dyn Jtag,
        byte_addr: u32,
        granule: Granularity,
        values: [u32; 2],
    ) -> OtpDaiResult<()> {
        Self::wait_for_idle(jtag)?;

        // Set the DAI address to write to.
        let dai_address_addr = Self::OTP_CTRL_BASE_ADDR + OtpCtrlReg::DirectAccessAddress as u32;
        jtag.write_memory32(dai_address_addr, &[byte_addr])
            .map_err(|source| OtpDaiError::Jtag { source })?;

        let dai_wdata0_addr = Self::OTP_CTRL_BASE_ADDR + OtpCtrlReg::DirectAccessWdata0 as u32;
        let dai_wdata1_addr = Self::OTP_CTRL_BASE_ADDR + OtpCtrlReg::DirectAccessWdata1 as u32;

        jtag.write_memory32(dai_wdata0_addr, &[values[0]])
            .map_err(|source| OtpDaiError::Jtag { source })?;

        if granule == Granularity::B64 {
            jtag.write_memory32(dai_wdata1_addr, &[values[1]])
                .map_err(|source| OtpDaiError::Jtag { source })?;
        }

        // Trigger a write command.
        let dai_cmd_addr = Self::OTP_CTRL_BASE_ADDR + OtpCtrlReg::DirectAccessCmd as u32;
        jtag.write_memory32(dai_cmd_addr, &[DirectAccessCmd::WR.bits()])
            .map_err(|source| OtpDaiError::Jtag { source })?;

        Self::wait_for_idle(jtag)?;

        Ok(())
    }

    /// Lock the partition starting at offset `byte_addr`.
    pub fn lock(jtag: &dyn Jtag, byte_addr: u32) -> OtpDaiResult<()> {
        Self::wait_for_idle(jtag)?;

        // Set the DAI address to the start of the partition.
        let dai_address_addr = Self::OTP_CTRL_BASE_ADDR + OtpCtrlReg::DirectAccessAddress as u32;
        jtag.write_memory32(dai_address_addr, &[byte_addr])
            .map_err(|source| OtpDaiError::Jtag { source })?;

        // Trigger a digest calculation command.
        let dai_cmd_addr = Self::OTP_CTRL_BASE_ADDR + OtpCtrlReg::DirectAccessCmd as u32;
        jtag.write_memory32(dai_cmd_addr, &[DirectAccessCmd::DIGEST.bits()])
            .map_err(|source| OtpDaiError::Jtag { source })?;

        Self::wait_for_idle(jtag)?;

        Ok(())
    }

    /// Wait for the OTP controller's status to read `DAI_IDLE`, showing it's
    /// ready to accept commands.
    pub fn wait_for_idle(jtag: &dyn Jtag) -> Result<(), OtpDaiError> {
        let otp_status_addr = Self::OTP_CTRL_BASE_ADDR + OtpCtrlReg::Status as u32;

        poll::poll_until(Self::POLL_TIMEOUT, Self::POLL_DELAY, || {
            let mut status = [0];
            jtag.read_memory32(otp_status_addr, &mut status)
                .map_err(|source| OtpDaiError::Jtag { source })?;

            let status =
                OtpCtrlStatus::from_bits(status[0]).context("status has invalid bits set")?;

            if status.intersects(OtpCtrlStatus::ERRORS) {
                bail!("status {status:#b} has error bits set");
            }

            Ok(status.contains(OtpCtrlStatus::DAI_IDLE))
        })
        .map_err(|source| OtpDaiError::WaitForIdle { source })
    }
}

pub type OtpDaiResult<T> = Result<T, OtpDaiError>;

/// Failures to write OTP parameters through the Direct Access Interface.
#[derive(Debug, Error)]
pub enum OtpDaiError {
    #[error("provided buffer has invalid size {buf_size} for parameter of size {param_size}")]
    BufSize { buf_size: usize, param_size: u32 },

    #[error("failed to communicate over JTAG")]
    Jtag { source: anyhow::Error },

    #[error("failed to wait for otp_ctrl DAI to be idle")]
    WaitForIdle { source: anyhow::Error },

    #[error("writing to otp_ctrl direct access registers is disabled")]
    WriteDisabled,
}
