// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use bitflags::bitflags;

bitflags! {
    #[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
    pub struct TpmAccess: u8 {
        const ESTABLISHMENT = 0x01;
        const REQUEST_USE = 0x02;
        const PENDING_REQUEST = 0x04;
        const SEIZE = 0x08;
        const BEEN_SEIZES = 0x10;
        const ACTIVE_LOCALITY = 0x20;
        const VALID = 0x80;
    }
}
