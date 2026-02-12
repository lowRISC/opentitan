// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use std::collections::HashMap;
use std::io::ErrorKind;
use std::path::Path;
use std::sync::LazyLock;

#[doc(hidden)]
pub struct BuiltinFile {
    pub name: &'static str,
    pub content: &'static str,
}
inventory::collect!(BuiltinFile);

#[doc(hidden)]
pub use inventory::submit;

/// Declare a built-in file.
///
/// All built-in files declared this way that gets linked will be accessible with
/// `/__builtin__/<file name>` path when handled by parts of OT that allows built-in files.
#[macro_export]
macro_rules! builtin_file {
    ($name: literal) => {
        $crate::util::fs::builtin_file!($name, include_str!($name));
    };

    ($name: literal, $content: expr) => {
        $crate::util::fs::submit!($crate::util::fs::BuiltinFile {
            name: $name,
            content: $content,
        });
    };
}
pub use crate::builtin_file;

static BUILTINS: LazyLock<HashMap<&'static str, &'static str>> = LazyLock::new(|| {
    inventory::iter::<BuiltinFile>()
        .map(|x| (x.name, x.content))
        .collect()
});

/// Equivalent to `std::fs::read_to_string`, but handle `/__builtin__` files.
pub fn read_to_string(path: &Path) -> std::io::Result<String> {
    if let Ok(builtin) = path.strip_prefix("/__builtin__") {
        Ok(BUILTINS
            .get(builtin.to_str().ok_or(ErrorKind::NotFound)?)
            .ok_or(ErrorKind::NotFound)?
            .to_string())
    } else {
        std::fs::read_to_string(path)
    }
}
