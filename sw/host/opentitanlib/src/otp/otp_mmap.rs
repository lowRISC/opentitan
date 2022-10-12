// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use crate::otp::otp_img::OtpImg;
use crate::otp::vmem_serialize::*;
use crate::util::num_de::{self, DeferredValue};

use anyhow::{anyhow, bail, Result};
use serde::Deserialize;
use std::collections::HashMap;
use std::convert::TryInto;
use std::fs;
use std::path::Path;

// FIXME: The OTP module is not being used yet.  When we write the OTP
// configuration utility, remove the `dead_code`s and clean up the warnings.

#[derive(Deserialize, Debug)]
struct OtpMapConfig {
    #[serde(deserialize_with = "num_de::deserialize")]
    width: usize,
    #[serde(deserialize_with = "num_de::deserialize")]
    depth: usize,
}

#[derive(Deserialize, Debug)]
struct OtpMapKey {
    name: String,
    value: DeferredValue,
}

#[derive(Deserialize, Debug)]
struct OtpMapDigest {
    name: String,
    iv_value: DeferredValue,
    cnst_value: DeferredValue,
}

#[derive(Deserialize, Debug)]
struct OtpMapScrambling {
    #[serde(deserialize_with = "num_de::deserialize")]
    key_size: usize,
    #[serde(deserialize_with = "num_de::deserialize")]
    iv_size: usize,
    #[serde(deserialize_with = "num_de::deserialize")]
    cnst_size: usize,
    keys: Vec<OtpMapKey>,
    digests: Vec<OtpMapDigest>,
}

#[derive(Deserialize, Debug)]
struct OtpMapItem {
    name: String,
    #[serde(deserialize_with = "num_de::deserialize")]
    size: usize,
    #[serde(default)]
    #[allow(dead_code)]
    isdigest: bool,
    #[allow(dead_code)]
    inv_default: Option<DeferredValue>,
}

#[derive(Deserialize, Debug)]
pub struct OtpMapPartition {
    name: String,
    #[allow(dead_code)]
    secret: bool,
    #[serde(default, deserialize_with = "num_de::deserialize")]
    size: usize,
    sw_digest: bool,
    hw_digest: bool,
    key_sel: String,
    items: Vec<OtpMapItem>,
}

#[derive(Deserialize, Debug)]
pub struct OtpMap {
    #[allow(dead_code)]
    seed: String,
    otp: OtpMapConfig,
    scrambling: OtpMapScrambling,
    partitions: Vec<OtpMapPartition>,
}

impl OtpMap {
    pub fn new(in_file: &Path) -> Result<OtpMap> {
        let json_text = fs::read_to_string(in_file)?;
        let res: OtpMap = deser_hjson::from_str(&json_text)?;
        Ok(res)
    }

    pub fn generate_keys(&self, img: &OtpImg) -> HashMap<String, Vec<u8>> {
        let mut rng = img.get_rng();
        let mut map = HashMap::new();
        for key in &self.scrambling.keys {
            let value = key.value.resolve(self.scrambling.key_size, &mut rng);
            map.insert(key.name.clone(), value);
        }
        map
    }

    pub fn make_vmem(&mut self, img: &mut OtpImg) -> Result<VmemImage> {
        // Seeded RNG needed for "<random>" values.
        let mut rng = img.get_rng();
        let mut vmem_partitions = Vec::<VmemPartition>::new();
        for partition in &self.partitions {
            let key_name = match partition.key_sel.as_str() {
                "NoKey" => None,
                key => Some(key.to_owned()),
            };

            let digest_type = if !partition.sw_digest && !partition.hw_digest {
                DigestType::Unlocked
            } else if partition.sw_digest && !partition.hw_digest {
                DigestType::Software
            } else if !partition.sw_digest && partition.hw_digest {
                // Extra information needed to compute HW digests.
                let iv_size = self.scrambling.iv_size;
                let cnst_size = self.scrambling.cnst_size;
                let digest_info = self
                    .scrambling
                    .digests
                    .iter_mut()
                    .find(|v| v.name == "CnstyDigest")
                    .ok_or_else(|| anyhow!("Couldn't find digest info"))?;

                const IV_SIZE: usize = std::mem::size_of::<DigestIV>();
                const CNST_SIZE: usize = std::mem::size_of::<DigestCnst>();
                let iv_value: [u8; IV_SIZE] = digest_info
                    .iv_value
                    .resolve(iv_size, &mut rng)
                    .try_into()
                    .map_err(|_| anyhow!("Bad IV size {}", iv_size))?;
                let cnst_value: [u8; CNST_SIZE] = digest_info
                    .cnst_value
                    .resolve(cnst_size, &mut rng)
                    .try_into()
                    .map_err(|_| anyhow!("Bad scrambling constant size {}", cnst_size))?;
                DigestType::Hardware(
                    DigestIV::from_ne_bytes(iv_value),
                    DigestCnst::from_ne_bytes(cnst_value),
                )
            } else {
                bail!("Invalid digest configuration");
            };

            let mut vmem_partition = VmemPartition::new(
                partition.name.clone(),
                partition.size,
                digest_type,
                key_name,
            );

            // Fetch the img definition for partition, this contains the associated values for
            // partition items.
            let mut img_partition = img.get_partition(&partition.name);

            let mut offset = 0usize;

            // Resolve all values and convert to Vmem representation.
            for item in &partition.items {
                let img_item_value = match &mut img_partition {
                    Some(v) => {
                        let item_value = v.get_item(&item.name);
                        match item_value {
                            Some(v) => v.value.resolve(item.size, &mut rng),
                            None => vec![0u8; item.size],
                        }
                    }
                    None => vec![0u8; item.size],
                };
                let vmem_item = VmemItem::new(img_item_value, offset, item.name.clone());
                offset += item.size;
                vmem_partition.push_item(vmem_item);
            }
            if partition.size == 0 {
                const SCRAMBLE_BLOCK_WIDTH: usize = 8;
                const DIGEST_SIZE: usize = 8;
                let mut size = SCRAMBLE_BLOCK_WIDTH
                    * ((offset + SCRAMBLE_BLOCK_WIDTH - 1) / SCRAMBLE_BLOCK_WIDTH);
                if partition.hw_digest || partition.sw_digest {
                    size += DIGEST_SIZE;
                }
                vmem_partition.set_size(size);
            }
            vmem_partitions.push(vmem_partition);
        }
        Ok(VmemImage::new(
            vmem_partitions,
            self.otp.width,
            self.otp.depth,
        ))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::testdata;
    use std::fs::read_to_string;

    #[test]
    fn test_mmap_deserialize() {
        let _: OtpMap =
            deser_hjson::from_str(&read_to_string(testdata!("otp_ctrl_mmap.hjson")).unwrap())
                .unwrap();
    }

    #[test]
    fn test_img_deserialize() {
        let _: OtpImg =
            deser_hjson::from_str(&read_to_string(testdata!("otp_ctrl_img_dev.hjson")).unwrap())
                .unwrap();
    }
}
