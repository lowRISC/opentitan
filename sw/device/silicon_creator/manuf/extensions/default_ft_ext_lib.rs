// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::Result;
use util_lib::response::PersonalizeResponse;

pub fn ft_ext(_response: &PersonalizeResponse) -> Result<Option<String>> {
    Ok(None)
}
