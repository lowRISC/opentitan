// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#![allow(unused_imports)]

pub mod app;

pub mod transport {
    pub mod common {
        #[path = "fpga.rs"]
        pub mod fpga;
        pub use opentitanlib_core::transport::common::*;
    }
    #[path = "ioexpander/mod.rs"]
    pub mod ioexpander;

    pub use opentitanlib_core::transport::*;
}

// Re-export core modules for internal use to avoid changing crate:: imports
pub(crate) use opentitanlib_core::collection;
pub(crate) use opentitanlib_core::crypto;
pub(crate) use opentitanlib_core::impl_serializable_error;
pub(crate) use opentitanlib_core::io;
pub(crate) use opentitanlib_core::regex;
pub(crate) use opentitanlib_core::util;
pub(crate) use opentitanlib_core::with_unknown;

// Re-export chip modules
pub(crate) use opentitanlib_chip::chip;
pub(crate) use opentitanlib_chip::otp;
pub(crate) use opentitanlib_chip::ownership;

// Re-export debug modules
pub(crate) use opentitanlib_debug::debug;
