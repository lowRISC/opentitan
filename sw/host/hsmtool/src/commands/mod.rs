// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::Result;
use atty::Stream;
use cryptoki::context::Pkcs11;
use cryptoki::session::Session;
use serde::{Deserialize, Serialize};
use serde_annotate::{Annotate, ColorProfile};
use std::any::Any;

mod token;

#[typetag::serde(tag = "command")]
pub trait Dispatch {
    fn run(
        &self,
        context: &dyn Any,
        pkcs11: &Pkcs11,
        session: Option<&Session>,
    ) -> Result<Box<dyn Annotate>>;
}

#[derive(clap::Subcommand, Debug, Serialize, Deserialize)]
pub enum Commands {
    #[command(subcommand)]
    Token(token::Token),
}

#[typetag::serde(name = "__commands__")]
impl Dispatch for Commands {
    fn run(
        &self,
        context: &dyn Any,
        pkcs11: &Pkcs11,
        session: Option<&Session>,
    ) -> Result<Box<dyn Annotate>> {
        match self {
            Commands::Token(x) => x.run(context, pkcs11, session),
        }
    }
}

#[derive(Debug, Serialize)]
pub struct BasicResult {
    success: bool,
    error: Option<String>,
}

impl BasicResult {
    pub fn from_error(e: &anyhow::Error) -> Box<dyn Annotate> {
        Box::new(BasicResult {
            success: false,
            error: Some(format!("{:?}", e)),
        })
    }
}

#[derive(clap::ValueEnum, Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum Format {
    Json,
    Json5,
    HJson,
    Yaml,
}

pub fn print_result(
    format: Format,
    color: Option<bool>,
    result: Result<Box<dyn Annotate>>,
) -> Result<()> {
    let (value, result) = match result {
        Ok(value) => (value, Ok(())),
        Err(e) => (BasicResult::from_error(&e), Err(e)),
    };

    let doc = serde_annotate::serialize(value.as_ref())?;
    let profile = if atty::is(Stream::Stdout) && color.unwrap_or(true) {
        ColorProfile::basic()
    } else {
        ColorProfile::default()
    };
    let string = match format {
        Format::Json => doc.to_json().color(profile).to_string(),
        Format::Json5 => doc.to_json5().color(profile).to_string(),
        Format::HJson => doc.to_hjson().color(profile).to_string(),
        Format::Yaml => doc.to_yaml().color(profile).to_string(),
    };
    println!("{}", string);
    result
}
