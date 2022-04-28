// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::Result;

use crate::app::TransportWrapper;
use crate::bootstrap::{Bootstrap, UpdateProtocol};
use crate::spiflash::SpiFlash;
use crate::transport::Capability;

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
    ) -> Result<()> {
        let spi = container.spi_params.create(transport)?;
        let flash = SpiFlash::from_spi(&*spi)?;
        flash.chip_erase(&*spi)?;
        flash.program(&*spi, 0, payload)?;
        SpiFlash::chip_reset(&*spi)?;
        Ok(())
    }
}
