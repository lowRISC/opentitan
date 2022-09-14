// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use serde::Deserialize;

use std::path::Path;

use crate::util::num_de::{DecEncoded, DeferredValue};
use anyhow::Result;
use rand::rngs::StdRng;
use rand::SeedableRng;

const OTP_IMG_SEED_DIVERSIFIER: u64 = 1941661965323525198146u128 as u64;

#[derive(Deserialize, Debug)]
pub struct OtpImgItem {
    pub name: String,
    pub value: DeferredValue,
}

#[derive(Deserialize, Debug)]
pub struct OtpImgPartition {
    pub name: String,
    pub items: Option<Vec<OtpImgItem>>,
}

#[derive(Deserialize, Debug)]
pub struct OtpImg {
    pub seed: DecEncoded<u64>,
    pub partitions: Vec<OtpImgPartition>,
}

pub trait OtpRead {
    fn read32(&self, name: &str) -> Result<u32> {
        self.read32_offset(Some(name), 0)
    }

    fn read32_offset(&self, name: Option<&str>, offset: usize) -> Result<u32>;
}

impl OtpImgPartition {
    pub fn get_item(&mut self, name: &str) -> Option<&mut OtpImgItem> {
        self.items
            .as_mut()
            .and_then(|items| items.iter_mut().find(|i| i.name == name))
    }
}

impl OtpImg {
    pub fn new(in_file: &Path) -> Result<OtpImg> {
        let json_text = std::fs::read_to_string(in_file)?;
        let res: OtpImg = deser_hjson::from_str(&json_text)?;
        Ok(res)
    }

    pub fn get_partition(&mut self, name: &str) -> Option<&mut OtpImgPartition> {
        self.partitions.iter_mut().find(|p| p.name == name)
    }

    pub fn partition(&self) -> &[OtpImgPartition] {
        &self.partitions
    }

    pub fn get_rng(&self) -> StdRng {
        StdRng::seed_from_u64(OTP_IMG_SEED_DIVERSIFIER + *self.seed)
    }
}
