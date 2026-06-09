// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
// Dummy comment to force rebuild


pub use opentitanlib_test_utils::test_utils;
pub mod transport;

// Re-export from core
pub use opentitanlib_core::collection;
pub use opentitanlib_core::crypto;
pub use opentitanlib_core::impl_serializable_error;
pub use opentitanlib_core::io;
pub use opentitanlib_core::regex;
pub use opentitanlib_core::transport as transport_core;
pub use opentitanlib_core::util;
pub use opentitanlib_core::with_unknown;

// Re-export from chip
pub use opentitanlib_chip::chip;
pub use opentitanlib_chip::otp;
pub use opentitanlib_chip::ownership;

// Re-export from debug
pub use opentitanlib_debug::debug;

// Re-export from app
pub use opentitanlib_app::app;

// Re-export from backend
pub use opentitanlib_backend::backend;
pub use opentitanlib_backend::define_interface;

// Re-export from image
pub use opentitanlib_image::image;

// Re-export from protocols
pub use opentitanlib_protocols::bootstrap;
pub use opentitanlib_protocols::console;
pub use opentitanlib_protocols::rescue;
pub use opentitanlib_protocols::spiflash;
pub use opentitanlib_protocols::tpm;
pub use opentitanlib_protocols::uart;
