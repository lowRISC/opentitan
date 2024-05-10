// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use sphincsplus_bindgen::SPX_BYTES;

pub fn do_something() -> u32 {
    SPX_BYTES
}

#[cfg(test)]
mod test {
    #[test]
    fn do_something_test() {
        assert_eq!(7856, super::do_something());
    }
}
