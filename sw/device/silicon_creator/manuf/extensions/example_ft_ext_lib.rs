// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::Result;
use arrayvec::ArrayVec;

pub fn ft_ext(endorsed_cert_concat: ArrayVec<u8, 4096>) -> Result<ArrayVec<u8, 4096>> {
    log::info!("Running example host FT extension ...");
    Ok(endorsed_cert_concat)
}
