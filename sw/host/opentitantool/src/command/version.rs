// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::Result;
use erased_serde::Serialize;
use regex::Regex;
use std::any::Any;
use std::collections::BTreeMap;
use structopt::StructOpt;

use opentitanlib::app::command::CommandDispatch;
use opentitanlib::app::TransportWrapper;

/// At compile time, the contents of `bazel-out/volatile-status.txt` is included, as if it was a
/// string literal in this file.  Bazel will not recompile this rust_binary solely because
/// `volatile-status.txt` has been updated, but any time this rust_binary is recompiled, it will
/// include the newest version of `volatile-status.txt`.
///
/// At runtime, this string is parsed into key/value pairs, which are returned.  (It would have
/// been desirable to perform the parsing at compile time as well.)
fn get_volatile_status() -> BTreeMap<&'static str, &'static str> {
    let volatile_status = include_str!("../../../../../bazel-out/volatile-status.txt");
    let re = Regex::new(r"([A-Z_]+) ([^\n]+)\n").unwrap();
    let mut properties: BTreeMap<&'static str, &'static str> = BTreeMap::new();
    for cap in re.captures_iter(volatile_status) {
        properties.insert(cap.get(1).unwrap().as_str(), cap.get(2).unwrap().as_str());
    }
    properties
}

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
    ) -> Result<Option<Box<dyn Serialize>>> {
        let properties = get_volatile_status();
        Ok(Some(Box::new(VersionResponse {
            version: properties.get("BUILD_GIT_VERSION").unwrap().to_string(),
            revision: properties.get("BUILD_SCM_REVISION").unwrap().to_string(),
            clean: *properties.get("BUILD_SCM_STATUS").unwrap() == "clean",
            timestamp: properties.get("BUILD_TIMESTAMP").unwrap().parse::<i64>()?,
        })))
    }
}
