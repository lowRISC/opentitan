// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::{Context, Result};
use cryptoki::context::CInitializeArgs;
use cryptoki::context::Pkcs11;
use cryptoki::session::Session;
use cryptoki::session::UserType;
use cryptoki::slot::Slot;
use serde::de::{Deserialize, Deserializer};

use crate::error::HsmError;

pub struct Module {
    pub pkcs11: Pkcs11,
}

impl Module {
    pub fn initialize(module: &str) -> Result<Self> {
        let mut pkcs11 = Pkcs11::new(module)?;
        pkcs11.initialize(CInitializeArgs::OsThreads)?;
        Ok(Module { pkcs11 })
    }

    pub fn get_token(&self, label: &str) -> Result<Slot> {
        let slots = self.pkcs11.get_slots_with_token()?;
        for slot in slots {
            let info = self.pkcs11.get_token_info(slot)?;
            if label == info.label() {
                return Ok(slot);
            }
        }
        Err(HsmError::TokenNotFound(label.into()).into())
    }

    pub fn connect(
        &self,
        token: &str,
        user: Option<UserType>,
        pin: Option<&str>,
    ) -> Result<Session> {
        let slot = self.get_token(token)?;
        let session = self.pkcs11.open_rw_session(slot)?;
        if let Some(user) = user {
            session.login(user, pin).context("Failed HSM Login")?;
        }
        Ok(session)
    }
}

pub fn parse_user_type(val: &str) -> Result<UserType> {
    match val {
        "So" | "SO" | "so" | "security_officer" => Ok(UserType::So),
        "User" | "USER" | "user" => Ok(UserType::User),
        _ => Err(HsmError::UnknownUser(val.into()).into()),
    }
}

pub fn deserialize_user<'de, D>(deserializer: D) -> std::result::Result<UserType, D::Error>
where
    D: Deserializer<'de>,
{
    let user = String::deserialize(deserializer)?;
    parse_user_type(&user).map_err(serde::de::Error::custom)
}
