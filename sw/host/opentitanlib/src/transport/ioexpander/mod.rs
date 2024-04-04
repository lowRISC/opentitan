// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use crate::app::config;
use crate::app::TransportWrapper;
use crate::io::ioexpander::IoExpander;

use anyhow::Result;

mod sx1503;

/// Creates an instance of `IoExpander` as specified in the given configuration declaration
/// section.  The `driver` field will decide the implementing struct.
pub fn create(
    conf: &config::IoExpander,
    transport_wrapper: &TransportWrapper,
) -> Result<IoExpander> {
    match conf.driver {
        config::IoExpanderDriver::Sx1503 => sx1503::create(conf, transport_wrapper),
        // Add future drivers here
    }
}
