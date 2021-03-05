// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#![deny(warnings)]
#![deny(unused)]
#![deny(unsafe_code)]

use std::env;
use std::fs;
use std::path::Path;

use rom_ext_config::parser::ParsedConfig;
use rom_ext_image::image::RawImage;

use mundane::hash::Sha256;
use mundane::public::rsa::RsaPkcs1v15;
use mundane::public::rsa::RsaPrivKey;
use mundane::public::rsa::RsaSignature;
use mundane::public::rsa::B3072;
use mundane::public::DerPrivateKey;
use mundane::public::Signature;

fn main() {
    let arg: String = env::args().nth(1).expect("Config path is missing");

    let config_path = Path::new(&arg);

    // Parse the config.
    let config = ParsedConfig::new(&config_path);

    // Read raw binary.
    let mut image = RawImage::new(&config.input_files.image_path);

    // Get the private key used for signature generation. It is also used to
    // extract key public exponent and modulus.
    let private_key_der =
        fs::read(&config.input_files.private_key_der_path).expect("Failed to read the image!");

    // Update "signed" manifest fields.
    image.update_static_fields(&config);

    // Convert ASN.1 DER private key into Mundane RsaPrivKey.
    let private_key =
        RsaPrivKey::parse_from_der(&private_key_der).expect("Failed to parse private key!");

    let mut exponent = private_key.public_exponent_be();
    // Encode public key components in little-endian byte order.
    exponent.reverse();
    image.update_exponent_field(&exponent);

    let mut modulus = private_key.public_modulus_be();
    // Encode public key components in little-endian byte order.
    modulus.reverse();
    image.update_modulus_field(&modulus);

    // Produce the signature from concatenated system_state_value,
    // device_usage_value and the portion of the "signed" portion of the image.
    let image_sign_data = image.data_to_sign();
    let device_usage_value = &device_usage_value(&config.input_files.usage_constraints_path);
    let system_state_value = &system_state_value(&config.input_files.system_state_value_path);

    let mut message_to_sign = Vec::<u8>::new();
    message_to_sign.extend_from_slice(system_state_value);
    message_to_sign.extend_from_slice(device_usage_value);
    message_to_sign.extend_from_slice(image_sign_data);

    let signature =
        RsaSignature::<B3072, RsaPkcs1v15, Sha256>::sign(&private_key, &message_to_sign)
            .expect("Failed to sign!");

    image.update_signature_field(&signature.bytes());

    // The whole image has been updated and signed, write the result to disk.
    image.write_file();
}

/// Generates the device usage value.
///
/// This value is extrapolated from the ROM_EXT manifest usage_constraints
/// field, and does not reside in the ROM_EXT manifest directly.
pub fn device_usage_value(path: &Path) -> Vec<u8> {
    let _usage_constraints = fs::read(path).expect("Failed to read usage constraints!");

    // TODO: generate the device_usage_value from usage_constraints.
    //       meanwhile use a "dummy" hard-coded vector.
    vec![0xA5; 1024]
}

/// Obtains the system state value from the binary on disk.
pub fn system_state_value(path: &Path) -> Vec<u8> {
    fs::read(path).expect("Failed to read system state value!")
}
