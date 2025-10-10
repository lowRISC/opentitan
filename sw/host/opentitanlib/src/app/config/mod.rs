// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::Result;
use std::path::{Path, PathBuf};
use thiserror::Error;

use crate::app::TransportWrapperBuilder;
use crate::util::fs::read_to_string;

mod structs;
pub use structs::*;

#[derive(Error, Debug)]
pub enum Error {
    #[error("No such configuration: `{0}`")]
    ConfigNotFound(PathBuf),
    #[error("Loading configuration file `{0}`: {1}")]
    ConfigReadError(PathBuf, anyhow::Error),
    #[error("Parsing configuration file `{0}`: {1}")]
    ConfigParseError(PathBuf, anyhow::Error),
}

pub fn process_config_file(env: &mut TransportWrapperBuilder, conf_file: &Path) -> Result<()> {
    log::debug!("Reading config file {:?}", conf_file);
    let conf_data = match read_to_string(conf_file) {
        Ok(v) => v,
        Err(e) if e.kind() == std::io::ErrorKind::NotFound => {
            Err(Error::ConfigNotFound(conf_file.to_owned()))?
        }
        Err(e) => Err(e)?,
    };
    let res: ConfigurationFile = serde_annotate::from_str(&conf_data)
        .map_err(|e| Error::ConfigParseError(conf_file.to_path_buf(), e.into()))?;

    let subdir = conf_file.parent().unwrap_or_else(|| Path::new(""));
    for included_conf_file in &res.includes {
        let path = subdir.join(included_conf_file);
        process_config_file(env, &path)?
    }
    env.add_configuration_file(res)
}
