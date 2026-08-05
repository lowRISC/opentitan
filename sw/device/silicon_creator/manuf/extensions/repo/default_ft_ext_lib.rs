// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::Result;
use arrayvec::ArrayVec;
use perso_tlv_lib::PersoBlobBuilder;
use util_lib::response::PersonalizeResponse;

pub fn ft_inject_certs_ext(perso_blob_builder: &mut PersoBlobBuilder) -> Result<()> {
    Ok(())
}

pub fn ft_post_boot_ext(_response: &PersonalizeResponse) -> Result<Option<String>> {
    Ok(None)
}
