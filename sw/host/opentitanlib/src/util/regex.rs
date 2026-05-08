// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#[macro_export]
macro_rules! regex {
    ($lit:literal) => {{
        static RE: ::std::sync::LazyLock<::regex::Regex> =
            ::std::sync::LazyLock::new(|| ::regex::Regex::new($lit).unwrap());
        &*RE
    }};
    (b; $lit:literal) => {{
        static RE: ::std::sync::LazyLock<::regex::bytes::Regex> =
            ::std::sync::LazyLock::new(|| ::regex::bytes::Regex::new($lit).unwrap());
        &*RE
    }};
}
