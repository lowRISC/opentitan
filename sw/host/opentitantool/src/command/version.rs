// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::Result;
use clap::Args;
use serde_annotate::Annotate;
use std::any::Any;

use opentitanlib::app::command::CommandDispatch;
use opentitanlib::app::TransportWrapper;

#[derive(Debug, Args)]
pub struct Version {}

#[derive(Debug, serde::Serialize)]
pub struct VersionResponse {
    pub version: String,
    pub revision: String,
    pub clean: bool,
    pub timestamp: i64,
}

impl Default for VersionResponse {
    fn default() -> Self {
        VersionResponse {
            version: std::env!("BUILD_GIT_VERSION").to_string(),
            revision: std::env!("BUILD_SCM_REVISION").to_string(),
            clean: std::env!("BUILD_SCM_STATUS") == "clean",
            timestamp: std::env!("BUILD_TIMESTAMP").parse::<i64>().unwrap(),
        }
    }
}

impl CommandDispatch for Version {
    fn run(
        &self,
        _context: &dyn Any,
        _transport: &TransportWrapper,
    ) -> Result<Option<Box<dyn Annotate>>> {
        Ok(Some(Box::<VersionResponse>::default()))
    }
}
