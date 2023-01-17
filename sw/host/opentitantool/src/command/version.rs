// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::Result;
use serde_annotate::Annotate;
use std::any::Any;
use structopt::StructOpt;

use opentitanlib::app::command::CommandDispatch;
use opentitanlib::app::TransportWrapper;

use dotenv;

/// At compile time, the contents of `bazel-out/volatile-status.txt` is included in
/// opentitantool.env, Bazel updates the fields in it if built with the --stamp flag set.
/// Bazel will not recompile this rust_binary solely because the values in opentitantool.env have
/// been updated, but any time this rust_binary is recompiled.
/// the timestamp is parsed at runtime.  (It would have
/// been desirable to perform the parsing at compile time as well.)
/// This is all compatible with the unstamped version of the values which will  leave the timestamp
/// as 0, clean = false,
/// BUILD_GIT_VERSION = {BUILD_GIT_VERSION} and BUILD_SCM_REVISION = {BUILD_SCM_REVISION}

#[derive(Debug, StructOpt)]
pub struct Version {}
#[derive(Debug, serde::Serialize)]
pub struct VersionResponse {
    version: String,
    revision: String,
    clean: bool,
    timestamp: i64,
}

impl CommandDispatch for Version {
    fn run(
        &self,
        _context: &dyn Any,
        _transport: &TransportWrapper,
    ) -> Result<Option<Box<dyn Annotate>>> {
        dotenv::dotenv().ok();
        let mut parsed_timestamp = 0;
        if option_env!("BUILD_TIMESTAMP").unwrap() != "{BUILD_TIMESTAMP}" {
            parsed_timestamp = option_env!("BUILD_TIMESTAMP").unwrap().parse::<i64>()?;
        }
        Ok(Some(Box::new(VersionResponse {
            version: option_env!("BUILD_GIT_VERSION").unwrap().to_string(),
            revision: option_env!("BUILD_SCM_REVISION").unwrap().to_string(),
            clean: option_env!("BUILD_SCM_STATUS").unwrap() == "clean",
            timestamp: parsed_timestamp,
        })))
    }
}
