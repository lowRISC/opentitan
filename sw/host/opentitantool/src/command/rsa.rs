// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::Result;
use serde_annotate::Annotate;
use std::any::Any;
use std::path::PathBuf;
use structopt::StructOpt;

use opentitanlib::app::command::CommandDispatch;
use opentitanlib::app::TransportWrapper;
use opentitanlib::crypto::rsa::{
    Exponent, Modulus, N0Inv, RsaPrivateKey, RsaPublicKey, Signature, RR,
};
use opentitanlib::crypto::sha256::Sha256Digest;
use opentitanlib::util::parse_int::ParseInt;

#[derive(serde::Serialize)]
pub struct RsaKeyInfo {
    pub key_num_bits: usize,
    pub modulus: Modulus,
    pub public_exponent: Exponent,
    pub n0_inv: N0Inv,
    pub rr: RR,
}

#[derive(serde::Serialize)]
pub struct RsaKeyInfoInWords {
    pub key_num_bits: usize,
    pub modulus: Vec<String>,
    pub public_exponent: Vec<String>,
    pub n0_inv: Vec<String>,
    pub rr: Vec<String>,
}

/// Show public information of a private or public RSA key
#[derive(Debug, StructOpt)]
pub struct RsaKeyShowCommand {
    #[structopt(
        name = "DER_FILE",
        help = "RSA public or private key file in DER format"
    )]
    der_file: PathBuf,
}

impl CommandDispatch for RsaKeyShowCommand {
    fn run(
        &self,
        _context: &dyn Any,
        _transport: &TransportWrapper,
    ) -> Result<Option<Box<dyn Annotate>>> {
        let key = match RsaPublicKey::from_pkcs1_der_file(&self.der_file) {
            Ok(key) => Ok(key),
            Err(_) => match RsaPrivateKey::from_pkcs8_der_file(&self.der_file) {
                Ok(key) => Ok(RsaPublicKey::from_private_key(&key)),
                Err(e) => Err(e),
            },
        }?;

        Ok(Some(Box::new(RsaKeyInfo {
            key_num_bits: key.modulus_num_bits(),
            modulus: key.modulus(),
            public_exponent: key.exponent(),
            n0_inv: key.n0_inv()?,
            rr: key.rr(),
        })))
    }
}

/// Generate a 3072-bit RSA public private key pair with exponent 65537. RSA private key will
/// be written to <OUTPUT_DIR>/<BASENAME>.der and RSA public key will be written to
/// <OUTPUT_DIR>/<BASENAME>.pub.der
#[derive(Debug, StructOpt)]
pub struct RsaKeyGenerateCommand {
    #[structopt(name = "OUTPUT_DIR", help = "Output directory")]
    output_dir: PathBuf,
    #[structopt(name = "BASENAME", help = "Basename for the generated key pair")]
    basename: String,
}

impl CommandDispatch for RsaKeyGenerateCommand {
    fn run(
        &self,
        _context: &dyn Any,
        _transport: &TransportWrapper,
    ) -> Result<Option<Box<dyn Annotate>>> {
        let private_key = RsaPrivateKey::new()?;
        let mut der_file = self.output_dir.to_owned();
        der_file.push(&self.basename);
        der_file.set_extension("der");
        private_key.to_pkcs8_der_file(&der_file)?;

        der_file.set_extension("pub.der");
        RsaPublicKey::from_private_key(&private_key).to_pkcs1_der_file(&der_file)?;

        Ok(None)
    }
}

#[derive(Debug, StructOpt, CommandDispatch)]
pub enum RsaKeySubcommands {
    Show(RsaKeyShowCommand),
    Generate(RsaKeyGenerateCommand),
}

#[derive(serde::Serialize)]
pub struct RsaSignResult {
    pub digest: String,
    pub signature: String,
}

#[derive(Debug, StructOpt)]
pub struct RsaSignCommand {
    #[structopt(
        name = "DER_FILE",
        parse(try_from_str=RsaPrivateKey::from_pkcs8_der_file),
        help = "RSA private key file in PKCS#1 DER format"
    )]
    private_key: RsaPrivateKey,
    #[structopt(
        name = "SHA256_DIGEST",
        parse(try_from_str=ParseInt::from_str),
        help = "SHA256 digest of the message"
    )]
    digest: Sha256Digest,
    #[structopt(
        name = "output",
        short,
        long,
        help = "File name to write the signature to"
    )]
    output: Option<PathBuf>,
}

impl CommandDispatch for RsaSignCommand {
    fn run(
        &self,
        _context: &dyn Any,
        _transport: &TransportWrapper,
    ) -> Result<Option<Box<dyn Annotate>>> {
        let signature = self.private_key.sign(&self.digest)?;
        if let Some(output) = &self.output {
            signature.write_to_file(output)?;
        }
        Ok(Some(Box::new(RsaSignResult {
            digest: self.digest.to_string(),
            signature: signature.to_string(),
        })))
    }
}

#[derive(Debug, StructOpt)]
pub struct RsaVerifyCommand {
    #[structopt(name = "KEY", help = "Key file in DER format")]
    der_file: PathBuf,
    #[structopt(
        name = "SHA256_DIGEST",
        help = "SHA256 digest of the message as a hex string (big-endian), i.e. 0x..."
    )]
    digest: String,
    #[structopt(
        name = "SIGNATURE",
        help = "Signature to be verified as a hex string (big-endian), i.e. 0x..."
    )]
    signature: String,
}

impl CommandDispatch for RsaVerifyCommand {
    fn run(
        &self,
        _context: &dyn Any,
        _transport: &TransportWrapper,
    ) -> Result<Option<Box<dyn Annotate>>> {
        let key = RsaPublicKey::from_pkcs1_der_file(&self.der_file)?;
        let digest = Sha256Digest::from_str(&self.digest)?;
        let signature = Signature::from_str(&self.signature)?;
        key.verify(&digest, &signature)?;
        Ok(None)
    }
}

#[derive(Debug, StructOpt, CommandDispatch)]
/// RSA commands.
#[allow(clippy::large_enum_variant)]
pub enum Rsa {
    Key(RsaKeySubcommands),
    Sign(RsaSignCommand),
    Verify(RsaVerifyCommand),
}
