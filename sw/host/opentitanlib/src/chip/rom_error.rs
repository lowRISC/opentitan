// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use crate::with_unknown;
use std::error::Error;

include!(env!("rom_error_enum"));

impl Error for RomError {}

impl From<RomError> for Result<(), RomError> {
    fn from(error: RomError) -> Self {
        if error == RomError::Ok {
            Ok(())
        } else {
            Err(error)
        }
    }
}

impl From<RomError> for Result<(), anyhow::Error> {
    fn from(error: RomError) -> Self {
        if error == RomError::Ok {
            Ok(())
        } else {
            Err(error.into())
        }
    }
}
