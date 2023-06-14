// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use crate::util::parse_int::ParseInt;

use std::fmt;
use std::path::Path;

use anyhow::{anyhow, bail, Result};

use serde::de::{self, Unexpected};
use serde::{Deserialize, Serialize};

use serde_annotate::Annotate;

#[derive(Annotate, Serialize, Debug, PartialEq, Eq)]
#[serde(untagged)]
pub enum OtpImgValue {
    Word(u64),
    Bool(bool),
    Sequence(Vec<u32>),
    #[serde(serialize_with = "serialize_random")]
    Random,
}

fn serialize_random<S>(serializer: S) -> Result<S::Ok, S::Error>
where
    S: serde::Serializer,
{
    serializer.serialize_str("<random>")
}

impl<'de> Deserialize<'de> for OtpImgValue {
    fn deserialize<D>(deserializer: D) -> Result<OtpImgValue, D::Error>
    where
        D: serde::Deserializer<'de>,
    {
        struct Visitor;

        impl<'a> de::Visitor<'a> for Visitor {
            type Value = OtpImgValue;

            fn expecting(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
                formatter.write_str("an OtpImgValue")
            }

            fn visit_str<E>(self, val: &str) -> Result<Self::Value, E>
            where
                E: de::Error,
            {
                Ok(match val {
                    "<random>" => OtpImgValue::Random,
                    "true" => OtpImgValue::Bool(true),
                    "false" => OtpImgValue::Bool(false),
                    _ => OtpImgValue::Word(
                        u64::from_str(val)
                            .map_err(|_| de::Error::invalid_value(Unexpected::Str(val), &self))?,
                    ),
                })
            }

            fn visit_u64<E>(self, val: u64) -> Result<Self::Value, E>
            where
                E: de::Error,
            {
                Ok(OtpImgValue::Word(val))
            }

            fn visit_bool<E>(self, val: bool) -> Result<Self::Value, E>
            where
                E: de::Error,
            {
                Ok(OtpImgValue::Bool(val))
            }

            fn visit_seq<A>(self, mut val: A) -> Result<Self::Value, A::Error>
            where
                A: de::SeqAccess<'a>,
            {
                let mut res = Vec::<u32>::new();
                while let Ok(Some(v)) = val.next_element::<String>() {
                    res.push(
                        u32::from_str(&v)
                            .map_err(|_| de::Error::invalid_value(Unexpected::Str(&v), &self))?,
                    )
                }
                Ok(OtpImgValue::Sequence(res))
            }
        }
        deserializer.deserialize_any(Visitor {})
    }
}

#[derive(Annotate, Serialize, Deserialize, Debug, PartialEq, Eq)]
pub struct OtpImgItem {
    pub name: String,
    pub value: OtpImgValue,
}

#[derive(Annotate, Serialize, Deserialize, Debug, PartialEq, Eq)]
pub struct OtpImgPartition {
    pub name: String,
    pub items: Option<Vec<OtpImgItem>>,
}

#[derive(Annotate, Serialize, Deserialize, Debug, PartialEq, Eq)]
pub struct OtpImg {
    #[serde(skip_serializing_if = "Option::is_none")]
    pub seed: Option<u64>,
    // FIXME: Needed to get `OtpImgValue` serailization to emit hex values.
    // See: https://github.com/cfrantz/serde-annotate/issues/5.
    #[annotate(format = hex)]
    pub partitions: Vec<OtpImgPartition>,
}

pub trait OtpRead {
    fn read32(&self, name: &str) -> Result<u32> {
        self.read32_offset(name, 0)
    }

    fn read32_offset(&self, name: &str, offset: usize) -> Result<u32>;
}

impl OtpRead for OtpImg {
    fn read32_offset(&self, name: &str, offset: usize) -> Result<u32> {
        if offset % 4 != 0 {
            bail!("offset not word aligned");
        }
        Ok(
            // Flatten all partitions and find the value that matches `name`.
            match self
                .partitions
                .iter()
                .filter_map(|p| p.items.as_ref())
                .flatten()
                .find(|v| v.name == name)
                .map(|item| &item.value)
            {
                Some(OtpImgValue::Word(v)) => {
                    if offset == 0 {
                        (v & u32::MAX as u64).try_into().unwrap()
                    } else if offset == 4 {
                        (v >> 32).try_into().unwrap()
                    } else {
                        bail!("invalid OTP address {} + {:#08x}", name, offset)
                    }
                }
                Some(OtpImgValue::Sequence(v)) => *v
                    .get(offset / 4)
                    .ok_or_else(|| anyhow!("invalid OTP address {} + {:#08x}", name, offset))?,
                None => bail!("undefined OTP word {}", name),
                Some(x) => bail!("invalid OTP word {} = {:?}", name, x),
            },
        )
    }
}

impl OtpImg {
    pub fn from_file(in_file: &Path) -> Result<OtpImg> {
        use std::str::FromStr;
        Self::from_str(&std::fs::read_to_string(in_file)?)
    }
}

impl std::str::FromStr for OtpImg {
    type Err = anyhow::Error;

    fn from_str(json_text: &str) -> Result<OtpImg> {
        let res: OtpImg = deser_hjson::from_str(json_text)?;
        Ok(res)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::str::FromStr;

    use serde_annotate::serialize;

    use once_cell::sync::Lazy;

    const TEST_OTP_JSON: &str = r#"
        {
            partitions: [
                {
                    name:  "CREATOR_SW_CFG",
                    items: [
                        {
                            name:  "CREATOR_SW_CFG_DIGEST",
                            value: 0,
                        },
                        {
                            name: "CREATOR_SW_CFG_SIGVERIFY_RSA_MOD_EXP_IBEX_EN",
                            value: "0x739",
                        },
                        {
                            name: "CREATOR_SW_CFG_SIGVERIFY_RSA_KEY_EN",
                            value: "0x4b4b4b4b4b4ba5a5",
                        },
                        {
                            name:  "CREATOR_RANDOM",
                            value: "<random>",
                        },
                        {
                            name:  "CREATOR_SEQ",
                            value: [
                                "0xab",
                                "0xcd",
                                "0xef",
                            ],
                        },
                    ]
                }
            ]
        }"#;

    static TEST_OTP: Lazy<OtpImg> = Lazy::new(|| OtpImg {
        seed: None,
        partitions: vec![OtpImgPartition {
            name: "CREATOR_SW_CFG".to_owned(),
            items: Some(vec![
                OtpImgItem {
                    name: "CREATOR_SW_CFG_DIGEST".to_owned(),
                    value: OtpImgValue::Word(0x0),
                },
                OtpImgItem {
                    name: "CREATOR_SW_CFG_SIGVERIFY_RSA_MOD_EXP_IBEX_EN".to_owned(),
                    value: OtpImgValue::Word(0x739),
                },
                OtpImgItem {
                    name: "CREATOR_SW_CFG_SIGVERIFY_RSA_KEY_EN".to_owned(),
                    value: OtpImgValue::Word(0x4b4b4b4b4b4ba5a5),
                },
                OtpImgItem {
                    name: "CREATOR_RANDOM".to_owned(),
                    value: OtpImgValue::Random,
                },
                OtpImgItem {
                    name: "CREATOR_SEQ".to_owned(),
                    value: OtpImgValue::Sequence(vec![0xab, 0xcd, 0xef]),
                },
            ]),
        }],
    });

    #[test]
    fn test_deser() {
        let res = OtpImg::from_str(TEST_OTP_JSON).unwrap();
        assert_eq!(res, *TEST_OTP);
    }

    #[test]
    fn test_ser() {
        let json = serialize(&*TEST_OTP).unwrap().to_hjson().to_string();
        let json_str = "{
  partitions: [
    {
      name: \"CREATOR_SW_CFG\",
      items: [
        {
          name: \"CREATOR_SW_CFG_DIGEST\",
          value: 0
        },
        {
          name: \"CREATOR_SW_CFG_SIGVERIFY_RSA_MOD_EXP_IBEX_EN\",
          value: 1849
        },
        {
          name: \"CREATOR_SW_CFG_SIGVERIFY_RSA_KEY_EN\",
          value: \"5425512962855773605\"
        },
        {
          name: \"CREATOR_RANDOM\",
          value: \"<random>\"
        },
        {
          name: \"CREATOR_SEQ\",
          value: [
            171,
            205,
            239
          ]
        }
      ]
    }
  ]
}";
        assert_eq!(json_str, json);
    }

    #[test]
    fn test_otp_read() {
        let otp = OtpImg::from_str(TEST_OTP_JSON).unwrap();
        assert_eq!(otp.read32("CREATOR_SW_CFG_DIGEST").unwrap(), 0x0);
        assert_eq!(
            otp.read32("CREATOR_SW_CFG_SIGVERIFY_RSA_MOD_EXP_IBEX_EN")
                .unwrap(),
            0x739
        );
        assert_eq!(
            otp.read32("CREATOR_SW_CFG_SIGVERIFY_RSA_KEY_EN").unwrap(),
            0x4b4ba5a5
        );
        assert_eq!(
            otp.read32_offset("CREATOR_SW_CFG_SIGVERIFY_RSA_KEY_EN", 4)
                .unwrap(),
            0x4b4b4b4b
        );
        assert!(otp.read32("CREATOR_RANDOM").is_err());
        assert_eq!(otp.read32_offset("CREATOR_SEQ", 0).unwrap(), 0xab);
        assert_eq!(otp.read32_offset("CREATOR_SEQ", 4).unwrap(), 0xcd);
        assert_eq!(otp.read32_offset("CREATOR_SEQ", 8).unwrap(), 0xef);
    }
}
