// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::{Context, Result};
use cryptoki::session::UserType;
use directories::ProjectDirs;
use serde::Deserialize;
use std::collections::HashMap;
use std::os::unix::fs::PermissionsExt;
use std::path::Path;

use crate::error::HsmError;
use crate::module;

#[derive(Deserialize)]
/// The HSM `Profile` contains authentication credentials for the named token.
///
/// The profiles file is a JSON map of profile names to per-token credentials:
/// ```ignore
/// {
///     "earlgrey": {
///         "token": "my_personal_token",
///         "user": "user",
///         "pin": "abc123"
///     }
/// }
/// ```
pub struct Profile {
    /// The name of the HSM token.
    pub token: String,

    /// The user type to authenticate to the token.
    #[serde(deserialize_with = "module::deserialize_user")]
    pub user: UserType,

    /// The pin for the user.
    pub pin: Option<String>,
}

impl Profile {
    pub fn load(filename: &Path) -> Result<HashMap<String, Profile>> {
        let path = if let Some(base) = ProjectDirs::from("org", "opentitan", "hsmtool") {
            base.config_dir().join(filename)
        } else {
            filename.to_owned()
        };
        let perm = path
            .metadata()
            .context(format!("Accessing {path:?}"))?
            .permissions()
            .mode()
            & 0o777;
        // Verify the profile is only accessible by owner.
        if perm & 0o077 != 0 {
            return Err(HsmError::FilePermissionError(perm)).context(format!("Accessing {path:?}"));
        }
        let profiles = std::fs::read_to_string(&path).context(format!("Cannot read {path:?}"))?;
        Ok(serde_annotate::from_str(&profiles)?)
    }
}
