use anyhow::Result;
use clap::Parser;
use elliptic_curve::pkcs8::DecodePrivateKey;
use elliptic_curve::SecretKey;
use num_bigint_dig::BigUint;
use p256::ecdsa::SigningKey;
use p256::NistP256;
use sha2::{Digest, Sha256};
use std::fs::File;
use std::io::{Read, Write};
use std::path::PathBuf;

use ot_certs::template::{EcdsaSignature, Signature, Value};
use ot_certs::x509::generate_certificate_from_tbs;

/// TBS signing command-line parameters.
#[derive(Debug, Parser)]
struct TbsSignInputs {
    /// Certificate endorsement ECC (P256) private key DER file.
    #[arg(long)]
    signing_key: PathBuf,

    /// Plain binary file containing the certificate TBS section.
    #[arg(long)]
    tbs: PathBuf,

    /// Output file to store the signed certificate.
    #[arg(long)]
    signed_cert: PathBuf,
}

fn run_ft_tbs_signer(host_ecc_sk: &PathBuf, tbs: &PathBuf) -> Result<Vec<u8>> {
    let mut file = File::open(tbs)?;

    // Read the file contents into a byte vector
    let mut tbs_bytes = Vec::new();
    file.read_to_end(&mut tbs_bytes)?;

    // Hash the TBS and convert the hash into big endian.
    let mut hasher = Sha256::new();
    hasher.update(&tbs_bytes);
    let tbs_digest = hasher.finalize();

    // Read the signing key data and create the proper structure.
    let host_sk = SecretKey::<NistP256>::read_pkcs8_der_file(host_ecc_sk)?;
    let signing_key = SigningKey::from(host_sk);

    let (tbs_signature, _) = signing_key.sign_prehash_recoverable(&tbs_digest)?;
    let (r, s) = tbs_signature.split_bytes();

    // Reformat the signature.
    let signature = Signature::EcdsaWithSha256 {
        value: Some(EcdsaSignature {
            r: Value::Literal(BigUint::from_bytes_be(&r)),
            s: Value::Literal(BigUint::from_bytes_be(&s)),
        }),
    };

    // Generate the endorsed certificate.
    generate_certificate_from_tbs(tbs_bytes, &signature)
}

fn main() -> Result<()> {
    let opts = TbsSignInputs::parse();

    let cert = run_ft_tbs_signer(&opts.signing_key, &opts.tbs)?;

    // Open or create the output file.
    let mut file = File::create(opts.signed_cert)?;

    // Write the byte vector to the file
    file.write_all(cert.as_slice())?;

    Ok(())
}
