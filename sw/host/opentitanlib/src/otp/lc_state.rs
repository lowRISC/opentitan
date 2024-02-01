// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::{bail, Result};
use serde::Deserialize;
use std::fs;
use std::path::Path;

/// SECDED matrix used for ECC in OTP.
#[derive(Deserialize, Debug)]
pub struct LcSecded {
    /// The number of bits of data covered by ECC.
    data_width: usize,
    /// The number of ECC bits.
    ecc_width: usize,
    /// ECC matrix used for computing ECC bits.
    ecc_matrix: Vec<Vec<u8>>,
}

/// The internal representation of lc_ctrl_state, used in OTP operations.
#[derive(Deserialize, Debug)]
pub struct LcState {
    secded: LcSecded,
}

#[repr(u32)]
#[derive(Copy, Clone)]
pub enum LcStateVal {
    Test = 0xb2865fbb,
    Dev = 0x0b5a75e0,
    Prod = 0x65f2520f,
    ProdEnd = 0x91b9b68a,
    Rma = 0xcf8cfaab,
}

impl LcSecded {
    pub fn new(in_file: &Path) -> Result<LcSecded> {
        let json_text = fs::read_to_string(in_file)?;
        let res: LcState = deser_hjson::from_str(&json_text)?;
        if res.secded.ecc_matrix.len() != res.secded.ecc_width {
            bail!("Bad ecc matrix length {}", res.secded.ecc_matrix.len());
        }
        Ok(res.secded)
    }

    fn bit_index(data: &[u8], index: usize) -> bool {
        let byte = index / 8;
        let bit = index % 8;
        data[byte] & (1 << bit) != 0
    }

    pub fn ecc_encode(&self, mut data: Vec<u8>) -> Result<Vec<u8>> {
        if data.len() * 8 != self.data_width {
            bail!("Bad data length for ecc {}", data.len() * 8);
        }
        let data_len = data.len();
        data.resize(data_len + self.ecc_byte_len(), 0);
        for (i, matrix) in self.ecc_matrix.iter().enumerate() {
            let mut bit = false;
            for j in matrix {
                bit ^= Self::bit_index(&data, *j as usize);
            }
            if bit {
                let byte = i / 8 + data_len;
                let bit = i % 8;
                data[byte] |= 1 << bit;
            }
        }

        Ok(data)
    }

    pub fn ecc_byte_len(&self) -> usize {
        if self.ecc_width == 0 {
            0
        } else {
            (self.ecc_width - 1) / 8 + 1
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::testdata;
    use anyhow::Result;
    use deser_hjson::from_str;
    use std::fs::read_to_string;

    #[test]
    fn test_lc_state_deserialize() -> Result<()> {
        let _: LcState = from_str(&read_to_string(testdata!("lc_ctrl_state.hjson"))?)?;
        Ok(())
    }

    #[test]
    fn test_ecc_encode() {
        let secded = LcSecded {
            data_width: 16,
            ecc_width: 6,
            ecc_matrix: vec![
                vec![0, 1, 3, 4, 6, 8, 10, 11, 13, 15], // ECC bit 0
                vec![0, 2, 3, 5, 6, 9, 10, 12, 13],     // ECC bit 1
                vec![1, 2, 3, 7, 8, 9, 10, 14, 15],     // ECC bit 2
                vec![4, 5, 6, 7, 8, 9, 10],             // ECC bit 3
                vec![11, 12, 13, 14, 15],               // ECC bit 4
                vec![
                    0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20,
                ], // Parity bit
            ],
        };

        let zero: Vec<u8> = vec![0, 0];
        let a5a5: Vec<u8> = vec![0xa5, 0xa5];
        let fcc5: Vec<u8> = vec![0xfc, 0xc5];
        assert_eq!(vec![0u8, 0, 0], secded.ecc_encode(zero).unwrap());
        assert_eq!(vec![0xa5u8, 0xa5, 0x27], secded.ecc_encode(a5a5).unwrap());
        assert_eq!(vec![0x0fcu8, 0xc5, 0x06], secded.ecc_encode(fcc5).unwrap())
    }
}
