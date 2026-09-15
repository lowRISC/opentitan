// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use indexmap::IndexMap;

pub mod provisioning_data;

/// Max sizes of the UJSON structs below when they are serialized.
///
/// The are obtained by running the following FPGA test:
/// bazel test --test_output=streamed \
///  //sw/device/silicon_creator/manuf/tests:ujson_msg_size_functest
///
/// These should match the constants in:
/// sw/device/lib/testing/json/provisioning_data.h
pub const SERDES_SHA256_HASH_SERIALIZED_MAX_SIZE: usize = 98;
pub const LC_TOKEN_HASH_SERIALIZED_MAX_SIZE: usize = 52;
pub const MANUF_CERTGEN_INPUTS_SERIALIZED_MAX_SIZE: usize = 321;
pub const PERSO_BLOB_SERIALIZED_MAX_SIZE: usize = 53303;

pub struct UjsonPayloads {
    /// HashMap of "Name" --> "UJSON data" sent from the Host to the Device
    /// during provisioning.
    pub dut_in: IndexMap<String, String>,
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_manuf_certgen_inputs_serialize_mldsa_key_id_present() {
        let inputs = provisioning_data::ManufCertgenInputs {
            dice_auth_key_key_id: arrayvec::ArrayVec::from([0x5a; 20]),
            ext_auth_key_key_id: arrayvec::ArrayVec::from([0xa5; 20]),
            dice_mldsa_auth_key_key_id: Some(arrayvec::ArrayVec::from([0xeb; 20])),
        };
        assert_eq!(
            serde_json::to_string(&inputs).expect("ManufCertgenInputs to serialize to JSON"),
            r#"{"dice_auth_key_key_id":[90,90,90,90,90,90,90,90,90,90,90,90,90,90,90,90,90,90,90,90],"ext_auth_key_key_id":[165,165,165,165,165,165,165,165,165,165,165,165,165,165,165,165,165,165,165,165],"dice_mldsa_auth_key_key_id":[235,235,235,235,235,235,235,235,235,235,235,235,235,235,235,235,235,235,235,235]}"#
        );

        let inputs = provisioning_data::ManufCertgenInputs {
            dice_auth_key_key_id: arrayvec::ArrayVec::from([0x5a; 20]),
            ext_auth_key_key_id: arrayvec::ArrayVec::from([0xa5; 20]),
            dice_mldsa_auth_key_key_id: Some(arrayvec::ArrayVec::from([0x00; 20])),
        };
        assert_eq!(
            serde_json::to_string(&inputs).expect("ManufCertgenInputs to serialize to JSON"),
            r#"{"dice_auth_key_key_id":[90,90,90,90,90,90,90,90,90,90,90,90,90,90,90,90,90,90,90,90],"ext_auth_key_key_id":[165,165,165,165,165,165,165,165,165,165,165,165,165,165,165,165,165,165,165,165],"dice_mldsa_auth_key_key_id":[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]}"#
        );
    }

    #[test]
    fn test_manuf_certgen_inputs_deserialize_mldsa_key_id_present() {
        let inputs: provisioning_data::ManufCertgenInputs = serde_json::from_str(r#"{"dice_auth_key_key_id":[90,90,90,90,90,90,90,90,90,90,90,90,90,90,90,90,90,90,90,90],"ext_auth_key_key_id":[165,165,165,165,165,165,165,165,165,165,165,165,165,165,165,165,165,165,165,165],"dice_mldsa_auth_key_key_id":[235,235,235,235,235,235,235,235,235,235,235,235,235,235,235,235,235,235,235,235]}"#).expect("JSON to deserialize to ManufCertgenInputs");
        assert_eq!(
            inputs.dice_auth_key_key_id,
            arrayvec::ArrayVec::from([0x5a; 20])
        );
        assert_eq!(
            inputs.ext_auth_key_key_id,
            arrayvec::ArrayVec::from([0xa5; 20])
        );
        assert_eq!(
            inputs.dice_mldsa_auth_key_key_id,
            Some(arrayvec::ArrayVec::from([0xeb; 20]))
        );

        let inputs: provisioning_data::ManufCertgenInputs = serde_json::from_str(r#"{"dice_auth_key_key_id":[90,90,90,90,90,90,90,90,90,90,90,90,90,90,90,90,90,90,90,90],"ext_auth_key_key_id":[165,165,165,165,165,165,165,165,165,165,165,165,165,165,165,165,165,165,165,165],"dice_mldsa_auth_key_key_id":[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]}"#).expect("JSON to deserialize to ManufCertgenInputs");
        assert_eq!(
            inputs.dice_auth_key_key_id,
            arrayvec::ArrayVec::from([0x5a; 20])
        );
        assert_eq!(
            inputs.ext_auth_key_key_id,
            arrayvec::ArrayVec::from([0xa5; 20])
        );
        assert_eq!(
            inputs.dice_mldsa_auth_key_key_id,
            Some(arrayvec::ArrayVec::from([0x00; 20]))
        );
    }

    #[test]
    fn test_manuf_certgen_inputs_serialize_mldsa_key_id_not_present() {
        let inputs = provisioning_data::ManufCertgenInputs {
            dice_auth_key_key_id: arrayvec::ArrayVec::from([0x5a; 20]),
            ext_auth_key_key_id: arrayvec::ArrayVec::from([0xa5; 20]),
            dice_mldsa_auth_key_key_id: None,
        };
        assert_eq!(
            serde_json::to_string(&inputs).expect("ManufCertgenInputs to serialize to JSON"),
            r#"{"dice_auth_key_key_id":[90,90,90,90,90,90,90,90,90,90,90,90,90,90,90,90,90,90,90,90],"ext_auth_key_key_id":[165,165,165,165,165,165,165,165,165,165,165,165,165,165,165,165,165,165,165,165]}"#
        );
    }

    #[test]
    fn test_manuf_certgen_inputs_deserialize_mldsa_key_id_not_present() {
        let inputs: provisioning_data::ManufCertgenInputs = serde_json::from_str(r#"{"dice_auth_key_key_id":[90,90,90,90,90,90,90,90,90,90,90,90,90,90,90,90,90,90,90,90],"ext_auth_key_key_id":[165,165,165,165,165,165,165,165,165,165,165,165,165,165,165,165,165,165,165,165]}"#).expect("JSON to deserialize to ManufCertgenInputs");
        assert_eq!(
            inputs.dice_auth_key_key_id,
            arrayvec::ArrayVec::from([0x5a; 20])
        );
        assert_eq!(
            inputs.ext_auth_key_key_id,
            arrayvec::ArrayVec::from([0xa5; 20])
        );
        assert_eq!(inputs.dice_mldsa_auth_key_key_id, None);
    }
}
