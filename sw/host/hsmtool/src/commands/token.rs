// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::Result;
use cryptoki::session::Session;
use serde::{Deserialize, Serialize};
use serde_annotate::Annotate;
use std::any::Any;

use crate::commands::Dispatch;
use crate::module::Module;

#[derive(clap::Args, Debug, Serialize, Deserialize)]
pub struct List;

#[derive(Debug, Serialize)]
pub struct TokenInfo {
    label: String,
    manufacturer_id: String,
    model: String,
    serial_number: String,
}

impl From<cryptoki::slot::TokenInfo> for TokenInfo {
    fn from(token: cryptoki::slot::TokenInfo) -> Self {
        TokenInfo {
            label: token.label().into(),
            manufacturer_id: token.manufacturer_id().into(),
            model: token.model().into(),
            serial_number: token.serial_number().into(),
        }
    }
}

#[derive(Debug, Default, Serialize)]
pub struct ListResponse {
    tokens: Vec<TokenInfo>,
}

#[typetag::serde(name = "token-list")]
impl Dispatch for List {
    fn run(
        &self,
        _context: &dyn Any,
        hsm: &Module,
        _session: Option<&Session>,
    ) -> Result<Box<dyn Annotate>> {
        let mut response = Box::<ListResponse>::default();
        for slot in hsm.pkcs11.get_slots_with_token()? {
            let info = hsm.pkcs11.get_token_info(slot)?;
            response.tokens.push(TokenInfo::from(info));
        }
        Ok(response)
    }
}

#[derive(clap::Subcommand, Debug, Serialize, Deserialize)]
pub enum Token {
    List(List),
}

#[typetag::serde(name = "__token__")]
impl Dispatch for Token {
    fn run(
        &self,
        context: &dyn Any,
        hsm: &Module,
        session: Option<&Session>,
    ) -> Result<Box<dyn Annotate>> {
        match self {
            Token::List(x) => x.run(context, hsm, session),
        }
    }
}
