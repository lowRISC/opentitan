// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::{bail, ensure, Result};
use std::convert::TryInto;

/// PRESENT block cipher.
///
/// Based on version 1.2 of the following Python implementation
/// https://github.com/doegox/python-cryptoplus
pub struct Present {
    round_keys: Vec<u64>,
}

impl Present {
    pub fn try_new_rounds(key: Vec<u8>, rounds: usize) -> Result<Present> {
        ensure!(
            (1..=254).contains(&rounds),
            "unsupported number of rounds {}",
            rounds
        );

        let round_keys = match key.len() {
            10 => generate_round_keys_80(key, rounds),
            16 => generate_round_keys_128(key, rounds),
            _ => bail!("key length must be 80 or 128 bits"),
        };

        Ok(Present { round_keys })
    }

    /// Create a new instance of the PRESENT cipher.
    ///
    /// Valid key lengths are 80 and 128 bits. All other key lengths will return an error.
    pub fn try_new(key: Vec<u8>) -> Result<Present> {
        Self::try_new_rounds(key, 32)
    }

    /// Create a new 128-bit PRESENT cipher instance.
    pub fn new_128(key: &[u8; 16]) -> Present {
        Self::try_new(key.to_vec()).unwrap()
    }

    /// Create a new 80-bit PRESENT cipher instance.
    pub fn new_80(key: &[u8; 10]) -> Present {
        Self::try_new(key.to_vec()).unwrap()
    }

    /// Encrypt a 64-bit block.
    pub fn encrypt_block(&self, block: u64) -> u64 {
        let mut state = block;
        state ^= self.round_keys[0];
        for round_key in &self.round_keys[1..] {
            state = s_box_layer(state);
            state = p_box_layer(state);
            state ^= round_key;
        }
        state
    }

    /// Decrypt a 64-bit block.
    pub fn decrypt_block(&self, block: u64) -> u64 {
        let mut state = block;
        for round_key in self.round_keys[1..].iter().rev() {
            state ^= round_key;
            state = p_box_layer_dec(state);
            state = s_box_layer_dec(state);
        }
        state ^ self.round_keys[0]
    }
}

const S_BOX: [u8; 16] = [
    0x0c, 0x05, 0x06, 0x0b, 0x09, 0x00, 0x0a, 0x0d, 0x03, 0x0e, 0x0f, 0x08, 0x04, 0x07, 0x01, 0x02,
];

const S_BOX_INV: [u8; 16] = [
    0x05, 0x0e, 0x0f, 0x08, 0x0c, 0x01, 0x02, 0x0d, 0x0b, 0x04, 0x06, 0x03, 0x00, 0x07, 0x09, 0x0a,
];

const P_BOX: [u8; 64] = [
    0x00, 0x10, 0x20, 0x30, 0x01, 0x11, 0x21, 0x31, 0x02, 0x12, 0x22, 0x32, 0x03, 0x13, 0x23, 0x33,
    0x04, 0x14, 0x24, 0x34, 0x05, 0x15, 0x25, 0x35, 0x06, 0x16, 0x26, 0x36, 0x07, 0x17, 0x27, 0x37,
    0x08, 0x18, 0x28, 0x38, 0x09, 0x19, 0x29, 0x39, 0x0a, 0x1a, 0x2a, 0x3a, 0x0b, 0x1b, 0x2b, 0x3b,
    0x0c, 0x1c, 0x2c, 0x3c, 0x0d, 0x1d, 0x2d, 0x3d, 0x0e, 0x1e, 0x2e, 0x3e, 0x0f, 0x1f, 0x2f, 0x3f,
];

const P_BOX_INV: [u8; 64] = [
    0x00, 0x04, 0x08, 0x0c, 0x10, 0x14, 0x18, 0x1c, 0x20, 0x24, 0x28, 0x2c, 0x30, 0x34, 0x38, 0x3c,
    0x01, 0x05, 0x09, 0x0d, 0x11, 0x15, 0x19, 0x1d, 0x21, 0x25, 0x29, 0x2d, 0x31, 0x35, 0x39, 0x3d,
    0x02, 0x06, 0x0a, 0x0e, 0x12, 0x16, 0x1a, 0x1e, 0x22, 0x26, 0x2a, 0x2e, 0x32, 0x36, 0x3a, 0x3e,
    0x03, 0x07, 0x0b, 0x0f, 0x13, 0x17, 0x1b, 0x1f, 0x23, 0x27, 0x2b, 0x2f, 0x33, 0x37, 0x3b, 0x3f,
];

/// Generate the round_keys for an 80-bit key.
fn generate_round_keys_80(key: Vec<u8>, rounds: usize) -> Vec<u64> {
    // Pad out key so it fits in a u128 later.
    let mut orig_key = key;
    let mut key = vec![0u8; 6];
    key.append(&mut orig_key);

    // Convert key into a u128 for easier bit manipulation.
    let key: &[u8; 16] = key.as_slice().try_into().unwrap();
    let mut key = u128::from_le_bytes(*key);

    let mut round_keys = Vec::new();
    for i in 1..rounds + 1 {
        // rawKey[0:64]
        let round_key = (key >> 16) as u64;

        // 1. Rotate bits
        // rawKey[19:len(rawKey)]+rawKey[0:19]
        key = (key & 0x7ffff) << 61 | key >> 19;

        // 2. SBox
        // rawKey[76:80] = S(rawKey[76:80])
        key = (S_BOX[(key >> 76) as usize] as u128) << 76 | (key & !0u128 >> (128 - 76));

        // 3. Salt
        // rawKey[15:20] ^ i
        key ^= (i as u128) << 15;

        round_keys.push(round_key);
    }

    round_keys
}

/// Generate the round_keys for a 128-bit key.
fn generate_round_keys_128(key: Vec<u8>, rounds: usize) -> Vec<u64> {
    let mut round_keys = Vec::new();

    // Convert key into a u128 for easier bit manipulation.
    let key: &[u8; 16] = key.as_slice().try_into().unwrap();
    let mut key = u128::from_le_bytes(*key);
    for i in 1..rounds + 1 {
        // rawKey[0:64]
        let round_key = (key >> 64) as u64;

        // 1. Rotate bits
        key = key.rotate_left(61);

        // 2. SBox
        key = (S_BOX[(key >> 124) as usize] as u128) << 124
            | (S_BOX[((key >> 120) & 0xF) as usize] as u128) << 120
            | (key & (!0u128 >> 8));

        // 3. Salt
        // rawKey[62:67] ^ i
        key ^= (i as u128) << 62;

        round_keys.push(round_key);
    }

    round_keys
}

/// SBox funciton for encryption.
fn s_box_layer(state: u64) -> u64 {
    let mut output: u64 = 0;
    for i in (0..64).step_by(4) {
        output |= (S_BOX[((state >> i) & 0x0f) as usize] as u64) << i;
    }
    output
}

/// SBox inverse function for decryption.
fn s_box_layer_dec(state: u64) -> u64 {
    let mut output: u64 = 0;
    for i in (0..64).step_by(4) {
        output |= (S_BOX_INV[((state >> i) & 0x0f) as usize] as u64) << i;
    }
    output
}

/// PBox function for encryption.
fn p_box_layer(state: u64) -> u64 {
    let mut output: u64 = 0;
    for (i, v) in P_BOX.iter().enumerate() {
        output |= ((state >> i) & 0x01) << v;
    }
    output
}

/// PBox inverse function for decryption.
fn p_box_layer_dec(state: u64) -> u64 {
    let mut output: u64 = 0;
    for (i, v) in P_BOX_INV.iter().enumerate() {
        output |= ((state >> i) & 0x01) << v;
    }
    output
}

#[cfg(test)]
mod test {
    use super::*;

    #[rustfmt::skip]
    const ROUND_KEYS_80: [u64; 32] = [
        0x0000000000000000, 0xc000000000000000, 0x5000180000000001, 0x60000a0003000001,
        0xb0000c0001400062, 0x900016000180002a, 0x0001920002c00033, 0xa000a0003240005b,
        0xd000d4001400064c, 0x30017a001a800284, 0xe01926002f400355, 0xf00a1c0324c005ed,
        0x800d5e014380649e, 0x4017b001abc02876, 0x71926802f600357f, 0x10a1ce324d005ec7,
        0x20d5e21439c649a8, 0xc17b041abc428730, 0xc926b82f60835781, 0x6a1cd924d705ec19,
        0xbd5e0d439b249aea, 0x07b077abc1a8736e, 0x426ba0f60ef5783e, 0x41cda84d741ec1d5,
        0xf5e0e839b509ae8f, 0x2b075ebc1d0736ad, 0x86ba2560ebd783ad, 0x8cdab0d744ac1d77,
        0x1e0eb19b561ae89b, 0xd075c3c1d6336acd, 0x8ba27a0eb8783ac9, 0x6dab31744f41d700,
    ];

    #[rustfmt::skip]
    const ROUND_KEYS_128: [u64; 32] = [
        0x0000000000000000, 0xcc00000000000000, 0xc300000000000000, 0x5b30000000000000,
        0x580c000000000001, 0x656cc00000000001, 0x6e60300000000001, 0xb595b30000000001,
        0xbeb980c000000002, 0x96d656cc00000002, 0x9ffae60300000002, 0x065b595b30000002,
        0x0f7feb980c000003, 0xac196d656cc00003, 0xa33dffae60300003, 0xd6b065b595b30003,
        0xdf8cf7feb980c004, 0x3b5ac196d656cc04, 0x387e33dffae60304, 0xeced6b065b595b34,
        0xe3e1f8cf7feb9809, 0x6bb3b5ac196d6569, 0xbb8f87e33dffae65, 0x80aeced6b065b590,
        0xc1ee3e1f8cf7febf, 0x2602bb3b5ac196d0, 0xcb07b8f87e33dffc, 0x34980aeced6b065d,
        0x8b2c1ee3e1f8cf78, 0x54d2602bb3b5ac1e, 0x4a2cb07b8f87e33a, 0x97534980aeced6b7,
    ];

    #[test]
    fn test_generate_80() {
        let key = vec![0u8; 10];
        let round_keys = generate_round_keys_80(key, 32);
        assert_eq!(round_keys, ROUND_KEYS_80);
    }

    #[test]
    fn test_generate_128() {
        let key = vec![0u8; 16];
        let round_keys = generate_round_keys_128(key, 32);
        assert_eq!(round_keys, ROUND_KEYS_128);
    }

    #[test]
    fn test_enc_80() -> Result<()> {
        let cipher = Present::try_new(vec![0; 10])?;
        assert_eq!(cipher.encrypt_block(0), 0x5579c1387b228445);
        Ok(())
    }

    #[test]
    fn test_dec_80() -> Result<()> {
        let cipher = Present::try_new(vec![0; 10])?;
        assert_eq!(cipher.decrypt_block(0x5579c1387b228445), 0);
        Ok(())
    }

    #[test]
    fn test_enc_128() -> Result<()> {
        let cipher = Present::try_new(vec![0; 16])?;
        assert_eq!(cipher.encrypt_block(0), 0x96db702a2e6900af);
        assert_eq!(cipher.encrypt_block(!0), 0x3c6019e5e5edd563);
        let cipher = Present::try_new(vec![0xff; 16])?;
        assert_eq!(cipher.encrypt_block(0), 0x13238c710272a5d8);
        assert_eq!(cipher.encrypt_block(!0), 0x628d9fbd4218e5b4);
        Ok(())
    }

    #[test]
    fn test_dec_128() -> Result<()> {
        let cipher = Present::try_new(vec![0; 16])?;
        assert_eq!(cipher.decrypt_block(0x96db702a2e6900af), 0);
        assert_eq!(cipher.decrypt_block(0x3c6019e5e5edd563), !0);
        let cipher = Present::try_new(vec![0xff; 16])?;
        assert_eq!(cipher.decrypt_block(0x13238c710272a5d8), 0);
        assert_eq!(cipher.decrypt_block(0x628d9fbd4218e5b4), !0);
        Ok(())
    }
}
