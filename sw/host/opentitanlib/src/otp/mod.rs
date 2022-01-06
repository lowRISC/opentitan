// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

pub mod lc_state;
pub mod otp;
pub mod otp_img;
pub mod otp_mmap;
pub mod vmem_serialize;

mod num_de;

#[cfg(test)]
mod tests {
    use super::*;
    use anyhow::Result;
    use std::path::Path;

    #[test]
    fn test_vmem_serialize() -> Result<()> {
        let mut otp_mmap = otp_mmap::OtpMap::new(Path::new("tests/otp_ctrl_mmap.hjson"))?;
        let mut otp_img = otp_img::OtpImg::new(Path::new("tests/otp_ctrl_img_dev.hjson"))?;
        let lc_state = lc_state::LcSecded::new(Path::new("tests/lc_ctrl_state.hjson"))?;
        let vmem = otp_mmap.make_vmem(&mut otp_img)?;
        let keys = otp_mmap.generate_keys(&otp_img);
        let result = vmem.generate(keys, &lc_state)?;
        let expected = std::fs::read_to_string(Path::new("tests/output.vmem"))?;
        let expected = expected
            .split("\n")
            .filter(|s| !s.is_empty())
            .collect::<Vec<&str>>();

        assert_eq!(result, expected);

        Ok(())
    }
}
