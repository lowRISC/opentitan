// Copyright lowRISC contributors (OpenTitan project).
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
    pub version: Option<String>,
    pub revision: Option<String>,
    pub clean: Option<bool>,
}

fn parse_variable(content: &str) -> Option<String> {
    // If stamping is disabled, the variable substition in stamp-env.txt
    // will not happen and the content of the environment variable will be
    // `{NAME_OF_VARIABLE}`. If we detect that this is the case, we return
    // None, otherwise we return the content.
    if content.starts_with('{') {
        None
    } else {
        Some(content.to_string())
    }
}

impl Default for VersionResponse {
    fn default() -> Self {
        VersionResponse {
            version: parse_variable(std::env!("BUILD_GIT_VERSION")),
            revision: parse_variable(std::env!("BUILD_SCM_REVISION")),
            clean: parse_variable(std::env!("BUILD_SCM_STATUS")).map(|x| x == "clean"),
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
