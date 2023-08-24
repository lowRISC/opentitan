// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::Result;
use once_cell::sync::Lazy;
use std::collections::HashMap;
use std::fs::File;
use std::io::Read;
use std::path::{Path, PathBuf};
use thiserror::Error;

use crate::app::TransportWrapperBuilder;
use crate::collection;

mod structs;
pub use structs::*;

#[derive(Error, Debug)]
pub enum Error {
    #[error("No such builtin configuration: `{0}`")]
    ConfigNotFound(PathBuf),
    #[error("Loading configuration file `{0}`: {1}")]
    ConfigReadError(PathBuf, anyhow::Error),
    #[error("Parsing configuration file `{0}`: {1}")]
    ConfigParseError(PathBuf, anyhow::Error),
}

fn read_into_string<'a>(path: &Path, s: &'a mut String) -> Result<&'a str> {
    let mut file = File::open(path)?;
    file.read_to_string(s)?;
    Ok(s.as_str())
}

pub fn process_config_file(env: &mut TransportWrapperBuilder, conf_file: &Path) -> Result<()> {
    log::debug!("Reading config file {:?}", conf_file);
    let mut string = String::new();
    let conf_data = if conf_file.starts_with("/__builtin__/") {
        let s = conf_file
            .to_str()
            .ok_or_else(|| Error::ConfigNotFound(conf_file.to_path_buf()))?;
        BUILTINS
            .get(s)
            .ok_or_else(|| Error::ConfigNotFound(conf_file.to_path_buf()))?
    } else {
        read_into_string(conf_file, &mut string)
            .map_err(|e| Error::ConfigReadError(conf_file.to_path_buf(), e))?
    };
    let res: ConfigurationFile = serde_annotate::from_str(conf_data)
        .map_err(|e| Error::ConfigParseError(conf_file.to_path_buf(), e.into()))?;

    let subdir = conf_file.parent().unwrap_or_else(|| Path::new(""));
    for included_conf_file in &res.includes {
        let path = subdir.join(included_conf_file);
        process_config_file(env, &path)?
    }
    env.add_configuration_file(res)
}

static BUILTINS: Lazy<HashMap<&'static str, &'static str>> = Lazy::new(|| {
    collection! {
        "/__builtin__/dediprog.json" => include_str!("dediprog.json"),
        "/__builtin__/h1dx_devboard.json" => include_str!("h1dx_devboard.json"),
        "/__builtin__/h1dx_devboard_c2d2.json" => include_str!("h1dx_devboard_c2d2.json"),
        "/__builtin__/servo_micro.json" => include_str!("servo_micro.json"),
        "/__builtin__/h1dx_devboard_ultradebug.json" => include_str!("h1dx_devboard_ultradebug.json"),
        "/__builtin__/ti50emulator.json" => include_str!("ti50emulator.json"),
        "/__builtin__/opentitan_cw310.json" => include_str!("opentitan_cw310.json"),
        "/__builtin__/opentitan_cw340.json" => include_str!("opentitan_cw340.json"),
        "/__builtin__/opentitan.json" => include_str!("opentitan.json"),
        "/__builtin__/hyperdebug_cw310.json" => include_str!("hyperdebug_cw310.json"),
        "/__builtin__/opentitan_ultradebug.json" => include_str!("opentitan_ultradebug.json"),
        "/__builtin__/opentitan_verilator.json" => include_str!("opentitan_verilator.json"),
    }
});
