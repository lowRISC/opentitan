// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Used for serde_annotate.
#![feature(min_specialization)]

// 1. Re-export core modules
pub use opentitanlib_core::{crypto, io, uart, util};
pub use opentitanlib_core::{impl_serializable_error, with_unknown, collection};

// 2. Re-export chip modules
pub use opentitanlib_chip::{chip, dif, image, ownership};

// 3. Re-export debug module
pub use opentitanlib_debug as debug;

// 4. Re-export app module
pub use opentitanlib_app as app;

// 5. Re-export protocol modules
pub use opentitanlib_protocols::{
    bootstrap, console, otp, proxy_server as proxy, rescue, spiflash, tpm,
};

// 6. Unified transport module (combines traits from core and drivers from transports)
pub mod transport {
    pub use opentitanlib_core::transport::{
        Bootstrap, Capabilities, Capability, EmptyTransport, NeededCapabilities, ProgressIndicator,
        SetJtagPins, Transport, TransportError, TransportInterfaceType, UpdateFirmware,
    };

    #[cfg(feature = "chip_whisperer")]
    pub use opentitanlib_transports::chip_whisperer;
    pub use opentitanlib_transports::common;
    #[cfg(feature = "dediprog")]
    pub use opentitanlib_transports::dediprog;
    #[cfg(feature = "ftdi")]
    pub use opentitanlib_transports::ftdi;
    #[cfg(feature = "hyperdebug")]
    pub use opentitanlib_transports::hyperdebug;
    pub use opentitanlib_transports::ioexpander;
    #[cfg(feature = "proxy")]
    pub use opentitanlib_transports::proxy;
    #[cfg(feature = "qemu")]
    pub use opentitanlib_transports::qemu;
    #[cfg(feature = "ti50emulator")]
    pub use opentitanlib_transports::ti50emulator;
    #[cfg(feature = "ultradebug")]
    pub use opentitanlib_transports::ultradebug;
    #[cfg(feature = "verilator")]
    pub use opentitanlib_transports::verilator;
}

// 7. Re-export backend module
pub use opentitanlib_backend as backend;

// 8. Re-export test_utils module
pub use opentitanlib_test_utils as test_utils;
