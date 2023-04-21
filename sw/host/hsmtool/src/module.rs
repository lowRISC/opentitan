// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::{Context, Result};
use cryptoki::context::CInitializeArgs;
use cryptoki::context::Pkcs11;
use cryptoki::session::Session;
use cryptoki::session::UserType;
use cryptoki::slot::Slot;

use crate::error::HsmError;

pub fn initialize(module: &str) -> Result<Pkcs11> {
    let mut pkcs11 = Pkcs11::new(module)?;
    pkcs11.initialize(CInitializeArgs::OsThreads)?;
    Ok(pkcs11)
}

pub fn get_token(pkcs11: &Pkcs11, label: &str) -> Result<Slot> {
    let slots = pkcs11.get_slots_with_token()?;
    for slot in slots {
        let info = pkcs11.get_token_info(slot)?;
        if label == info.label() {
            return Ok(slot);
        }
    }
    Err(HsmError::TokenNotFound(label.into()).into())
}

pub fn connect(
    pkcs11: &Pkcs11,
    token: &str,
    user: Option<UserType>,
    pin: Option<&str>,
) -> Result<Session> {
    let slot = get_token(pkcs11, token)?;
    let session = pkcs11.open_rw_session(slot)?;
    if let Some(user) = user {
        session.login(user, pin).context("Failed HSM Login")?;
    }
    Ok(session)
}

pub fn parse_user_type(val: &str) -> Result<UserType> {
    match val {
        "So" | "SO" | "so" | "security_officer" => Ok(UserType::So),
        "User" | "USER" | "user" => Ok(UserType::User),
        _ => Err(HsmError::UnknownUser(val.into()).into()),
    }
}
