// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::{Result, anyhow};

use crate::app::TransportWrapper;
use crate::bootstrap::{Bootstrap, UpdateProtocol};
use crate::spiflash::SpiFlash;
use crate::transport::{Capability, ProgressIndicator};

/// Implements the SPI EEPROM bootstrap protocol.
pub struct Eeprom;

impl Eeprom {
    /// Creates a new `Eeprom` protocol updater.
    pub fn new() -> Self {
        Eeprom
    }
}

impl UpdateProtocol for Eeprom {
    fn verify_capabilities(
        &self,
        _container: &Bootstrap,
        transport: &TransportWrapper,
    ) -> Result<()> {
        transport
            .capabilities()?
            .request(Capability::GPIO | Capability::SPI)
            .ok()?;
        Ok(())
    }

    fn uses_common_bootstrap_reset(&self) -> bool {
        true
    }

    /// Performs the update protocol using the `transport` with the firmware `payload`.
    fn update(
        &self,
        container: &Bootstrap,
        transport: &TransportWrapper,
        payload: &[u8],
        progress: &dyn ProgressIndicator,
        check_jedec_id: bool,
    ) -> Result<()> {
        let spi = container.spi_params.create(transport, "BOOTSTRAP")?;
        let flash = SpiFlash::from_spi(&*spi)?;
        if check_jedec_id {
            // Just in case, verify that we're talking to a lowRISC chip. Jedec ID
            // size of lowRISC SPI Flash impersonation is 15 bytes long.
            let v = SpiFlash::read_jedec_id(&*spi, 15)?;
            match (v[11], v[12], v[14]) {
                (127, 239, 20) => (), // The preamble is 12 bytes long, 239 is lowRISC assigned ID, 2^20 is flash size.
                (_, _, _) => {
                    // Print meaningful fileds from the collected ID.
                    let trimmed_jedec_id = match v.iter().rposition(|&x| x != 0) {
                        Some(idx) => &v[..=idx],
                        None => &[],
                    };
                    return Err(anyhow!(
                        "Unexpected JedecID on SPI bus: {:?}",
                        trimmed_jedec_id
                    ));
                }
            }
        }
        flash.chip_erase(&*spi)?;
        flash.program_with_progress(&*spi, 0, payload, progress)?;
        SpiFlash::chip_reset(&*spi)?;
        Ok(())
    }
}
