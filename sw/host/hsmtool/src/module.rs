// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::{Context, Result};
use cryptoki::context::CInitializeArgs;
use cryptoki::context::Pkcs11;
use cryptoki::session::Session;
use cryptoki::session::UserType;
use cryptoki::slot::Slot;
use cryptoki::types::AuthPin;
use serde::de::{Deserialize, Deserializer};
use std::rc::Rc;
use std::str::FromStr;

use crate::error::HsmError;
use crate::spxef::SpxEf;
use acorn::{Acorn, SpxInterface};

#[derive(Debug, Clone)]
pub enum SpxModule {
    Acorn(String),
    Pkcs11Ef,
}

impl SpxModule {
    pub const HELP: &'static str =
        "Type of sphincs+ module [allowed values: acorn:<libpath>, pkcs11-ef]";
}

impl FromStr for SpxModule {
    type Err = HsmError;
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        if s[..6].eq_ignore_ascii_case("acorn:") {
            Ok(SpxModule::Acorn(s[6..].into()))
        } else if s.eq_ignore_ascii_case("pkcs11-ef") {
            Ok(SpxModule::Pkcs11Ef)
        } else {
            Err(HsmError::ParseError(format!("unknown SpxModule {s:?}")))
        }
    }
}

pub struct Module {
    pub pkcs11: Pkcs11,
    pub session: Option<Rc<Session>>,
    pub acorn: Option<Box<dyn SpxInterface>>,
    pub token: Option<String>,
}

impl Module {
    pub fn initialize(module: &str) -> Result<Self> {
        let pkcs11 = Pkcs11::new(module)?;
        pkcs11.initialize(CInitializeArgs::OsThreads)?;
        Ok(Module {
            pkcs11,
            session: None,
            acorn: None,
            token: None,
        })
    }

    pub fn initialize_spx(&mut self, module: &SpxModule) -> Result<()> {
        let module = match module {
            SpxModule::Acorn(libpath) => Acorn::new(libpath)? as Box<dyn SpxInterface>,
            SpxModule::Pkcs11Ef => {
                let session = self
                    .session
                    .as_ref()
                    .map(Rc::clone)
                    .ok_or(HsmError::SessionRequired)?;
                SpxEf::new(session) as Box<dyn SpxInterface>
            }
        };
        self.acorn = Some(module);
        Ok(())
    }

    pub fn get_session(&self) -> Option<&Session> {
        self.session.as_ref().map(Rc::as_ref)
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
        &mut self,
        token: &str,
        user: Option<UserType>,
        pin: Option<&str>,
    ) -> Result<()> {
        let slot = self.get_token(token)?;
        let session = self.pkcs11.open_rw_session(slot)?;
        if let Some(user) = user {
            let pin = pin.map(|x| AuthPin::new(x.to_owned()));
            session
                .login(user, pin.as_ref())
                .context("Failed HSM Login")?;
        }
        self.token = Some(token.into());
        self.session = Some(Rc::new(session));
        Ok(())
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
