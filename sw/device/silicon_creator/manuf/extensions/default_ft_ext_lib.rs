// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::Result;
use arrayvec::ArrayVec;
use util_lib::response::PersonalizeResponse;

pub fn ft_inject_certs_ext(endorsed_cert_concat: ArrayVec<u8, 5120>) -> Result<ArrayVec<u8, 5120>> {
    Ok(endorsed_cert_concat)
}

pub fn ft_post_boot_ext(_response: &PersonalizeResponse) -> Result<Option<String>> {
    Ok(None)
}
