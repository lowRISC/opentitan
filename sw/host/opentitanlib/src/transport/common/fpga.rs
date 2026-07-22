// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::Result;

use crate::app::TransportWrapper;
use crate::io::fpga_backdoor::{BackdoorParams, enter_backdoor_loader};
use crate::io::jtag::JtagParams;
use crate::transport::ProgressIndicator;
use crate::util::usr_access::usr_access_get;

/// Command for Transport::dispatch().
pub struct FpgaProgram {
    /// The bitstream content to load into the FPGA.
    pub bitstream: Vec<u8>,
    /// A progress function to provide user feedback.
    /// Will be called with the address and length of each chunk sent to the target device.
    pub progress: Box<dyn ProgressIndicator>,
}

impl FpgaProgram {
    /// Strap into the bkdr_loader TAP and read the FPGA's `USR_ACCESS_TIMESTAMP` register.
    /// If the FPGA has no bitstream loaded at all (e.g. right after power-up), the
    /// `fpga_backdoor.tap` won't be present on the JTAG scan chain, so this fails outright
    /// rather than returning a value.
    fn read_fpga_usr_access(transport: &TransportWrapper, jtag_params: &JtagParams) -> Result<u32> {
        enter_backdoor_loader(transport)?;
        let backdoor_params = BackdoorParams {
            jtag: jtag_params.clone(),
        };
        let mut backdoor = backdoor_params.create(transport)?.connect(false)?;
        let usr_access = backdoor.read_usr_access_timestamp()?;
        backdoor.set_done()?;
        Ok(usr_access)
    }

    /// Check whether the FPGA is already configured with this bitstream, by strapping into the
    /// bkdr_loader TAP and comparing its `USR_ACCESS_TIMESTAMP` register against the `USR_ACCESS`
    /// value embedded in this bitstream file.
    ///
    /// Any failure to read that register (e.g. no bitstream loaded yet, so the scan chain
    /// doesn't even contain the backdoor TAP) is treated as "not the right bitstream": we fall
    /// back to reprogramming rather than propagating the error.
    fn check_correct_version(
        &self,
        transport: &TransportWrapper,
        jtag_params: &JtagParams,
    ) -> Result<bool> {
        let expected = usr_access_get(&self.bitstream)?;

        let actual = match Self::read_fpga_usr_access(transport, jtag_params) {
            Ok(actual) => actual,
            Err(e) => {
                log::debug!("Could not read USR_ACCESS_TIMESTAMP over the backdoor TAP: {e:#}");
                log::info!("Assuming no (or an incompatible) bitstream is currently loaded.");
                return Ok(false);
            }
        };

        if actual == expected {
            log::info!(
                "Already running the correct bitstream (USR_ACCESS_TIMESTAMP=0x{actual:08x}). Skip loading bitstream."
            );
            return Ok(true);
        }
        log::info!(
            "Bitstream USR_ACCESS_TIMESTAMP mismatch (running=0x{actual:08x}, expected=0x{expected:08x}); reprogramming."
        );
        Ok(false)
    }

    fn skip(&self) -> bool {
        self.bitstream.starts_with(b"__skip__")
    }

    pub fn should_skip(
        &self,
        transport: &TransportWrapper,
        jtag_params: &JtagParams,
    ) -> Result<bool> {
        if self.skip() {
            log::info!("Skip loading the __skip__ bitstream.");
            return Ok(true);
        }
        if self.check_correct_version(transport, jtag_params)? {
            return Ok(true);
        }
        Ok(false)
    }
}
