// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

//! The `util::attribute` module provides helpers for working with PKCS11
//! structs and identifiers as text (e.g. either in a CLI or as serialized
//! forms like json).
//!
//! The following enums & structs are equivalent to their corresponding
//! enums/structs in `cryptoki`:
//! - AttributeType
//! - CertificateType
//! - Date
//! - KeyType
//! - MechanismType
//! - ObjectClass
//!
//! They implement `From` for converting from their corresponding `cryptoki`
//! types and `TryFrom` (and `TryInto`) for converting back to the
//! `cryptoki` types.
//!
//! The `hsmtool` versions of these types provide integer conversion
//! to/from the cryptoki_sys types, and `serde::{Serialize, Deserialize}`.
//! They can also optionally provide `FromStr` and `Display` and can
//! support conversions from nicer names than the formal PKCS11 names
//! (like `CKK_RSA`).
//!
//! Just as the `cryptoki` types are thin wrappers around the PKCS11
//! C types, using their underlying C types inside the wrapper, the
//! `hsmtool` versions of these types are also wrappers around the
//! same underlying C types and use the same internal representation.
//!
//! The `cryptoki` APIs typically use `&[Attribute]` when passing
//! attributes to its functions.  For the purpose of building and
//! (de)serializing an Attribute list, a map is more convenient
//! structure and `AttributeMap` and `AttrData` fill that role.

mod attr;
mod attribute_type;
mod certificate_type;
mod data;
mod date;
mod error;
mod key_type;
mod mechanism_type;
mod object_class;

pub use attr::AttributeMap;
pub use data::{AttrData, Redacted};
pub use error::AttributeError;

pub use attribute_type::AttributeType;
pub use certificate_type::CertificateType;
pub use date::Date;
pub use key_type::KeyType;
pub use mechanism_type::MechanismType;
pub use object_class::ObjectClass;
