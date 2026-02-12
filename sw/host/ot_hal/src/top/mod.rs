// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

mod autogen;

pub mod earlgrey {
    #[cfg(not(feature = "english_breakfast"))]
    pub use super::autogen::earlgrey::{
        DirectPads, MuxedPads, PinmuxInsel, PinmuxMioOut, PinmuxOutsel, PinmuxPeripheralIn,
    };
    pub use top_earlgrey::top_earlgrey::*;
}
