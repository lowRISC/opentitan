// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

//! This crate handles generating OpenTitan certificates.
//!
//! These certificates are generated from a template and embedded onto an
//! OpenTitan device.
//!
//! Templates may specify that some values are variables, in which case they
//! will be filled in by the device itself. This crate will generate C code for
//! setting/getting variable values of templates from OpenTitan firmware.
//!
//! Certificates are generated in both X.509 format and CWT (CBOR web token)
//! format. Details of the certificates will be available in the documentation
//! in the future.

pub mod template;
pub mod x509;
