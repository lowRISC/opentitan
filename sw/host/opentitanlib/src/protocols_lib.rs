// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

pub mod bootstrap;
pub mod console;
pub mod rescue;
pub mod spiflash;
pub mod tpm;
pub mod uart;

// Re-export core modules for internal use to avoid changing crate:: imports
pub(crate) use opentitanlib_core::impl_serializable_error;
pub(crate) use opentitanlib_core::io;
pub(crate) use opentitanlib_core::regex;
pub(crate) use opentitanlib_core::transport;
pub(crate) use opentitanlib_core::util;
pub(crate) use opentitanlib_core::with_unknown;

// Re-export app modules for internal use
pub(crate) use opentitanlib_app::app;

// Re-export chip modules for internal use
pub(crate) use opentitanlib_chip::chip;
