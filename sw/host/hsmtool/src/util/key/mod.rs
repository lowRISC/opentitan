// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use clap;
use serde::{Deserialize, Serialize};

pub mod ecdsa;
pub mod rsa;

#[derive(clap::ValueEnum, Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum KeyEncoding {
    /// When saving, Pem means Pkcs8Pem.
    #[serde(alias = "pem")]
    Pem,
    /// When saving, Der means Pkcs8Der.
    #[serde(alias = "der")]
    Der,
    /// When saving, Pkcs1 means Pkcs1Pem.
    #[serde(alias = "pkcs1")]
    Pkcs1,
    /// When saving, Pkcs8 means Pkcs8Pem.
    #[serde(alias = "pkcs8")]
    Pkcs8,
    /// Pcks1 encoding in a PEM container.
    #[serde(alias = "pkcs1-pem")]
    Pkcs1Pem,
    /// Pcks8 encoding in a PEM container.
    #[serde(alias = "pkcs8-pem")]
    Pkcs8Pem,
    /// Pcks1 encoding in a DER container.
    #[serde(alias = "pkcs1-der")]
    Pkcs1Der,
    /// Pcks8 encoding in a DER container.
    #[serde(alias = "pkcs8-der")]
    Pkcs8Der,
}
