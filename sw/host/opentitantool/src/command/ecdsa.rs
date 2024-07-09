// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::{bail, Result};
use clap::{Args, Subcommand};
use regex::Regex;
use serde_annotate::Annotate;
use std::any::Any;
use std::fs::File;
use std::io::Write;
use std::path::{Path, PathBuf};

use opentitanlib::app::command::CommandDispatch;
use opentitanlib::app::TransportWrapper;
use opentitanlib::crypto::ecdsa::{
    EcdsaPrivateKey, EcdsaPublicKey, EcdsaRawPublicKey, EcdsaRawSignature,
};
use opentitanlib::crypto::sha256::Sha256Digest;
use opentitanlib::util::parse_int::ParseInt;

/// Given the path to a public key, returns the public key. Given
/// the path to a private key, extracts the public key from the private
/// key and returns the public key.
fn load_pub_or_priv_key(path: &Path) -> Result<EcdsaPublicKey> {
    if let Ok(key) = EcdsaPublicKey::load(path) {
        return Ok(key);
    }
    let key = EcdsaPrivateKey::load(path)?;
    Ok(key.public_key())
}

/// Show public information of a private or public ECDSA key
#[derive(Debug, Args)]
pub struct EcdsaKeyShowCommand {
    /// ECDSA public or private key file in DER format.
    der_file: PathBuf,
}

#[derive(serde::Serialize, Annotate)]
pub struct EcdsaKeyShowResult {
    pub raw: EcdsaRawPublicKey,
    #[serde(with = "serde_bytes")]
    #[annotate(format = hexstr)]
    pub sec1_encoded: Vec<u8>,
    #[annotate(comment = "Formatted for use in OTP configuration")]
    pub otp_encoded: String,
}

impl CommandDispatch for EcdsaKeyShowCommand {
    fn run(
        &self,
        _context: &dyn Any,
        _transport: &TransportWrapper,
    ) -> Result<Option<Box<dyn Annotate>>> {
        let key = load_pub_or_priv_key(&self.der_file)?;

        // The OTP creation tool is written in python and parses arbitrary
        // sized integers using python's `int` constructor and then writes
        // the values into the OTP image as little-endian values.
        //
        // We want to store into OTP the little-endian representations of
        // the key's X and Y values.  Therefore, we emit the key as the
        // big-endian representation `KEY = (Y || X)` so that when the OTP tool
        // writes the little-endian representation of `KEY` into OTP, the
        // resulting data will be `little-endian(X) || little-endian(Y)`.
        let mut otp = Vec::new();
        let point = key.key.to_encoded_point(false);
        otp.extend_from_slice(point.y().unwrap().as_slice());
        otp.extend_from_slice(point.x().unwrap().as_slice());
        let otp = format!("0x{}", hex::encode(otp));

        Ok(Some(Box::new(EcdsaKeyShowResult {
            raw: EcdsaRawPublicKey::try_from(&key)?,
            sec1_encoded: key.key.to_sec1_bytes().to_vec(),
            otp_encoded: otp,
        })))
    }
}

/// Generate a NIST P-256 ECDSA key. The private key will be written to
/// <OUTPUT_DIR>/<BASENAME>.der and the public key will be written to
/// <OUTPUT_DIR>/<BASENAME>.pub.der
#[derive(Debug, Args)]
pub struct EcdsaKeyGenerateCommand {
    /// Output directory.
    output_dir: PathBuf,
    /// Basename for the generated key pair.
    basename: String,
}

impl CommandDispatch for EcdsaKeyGenerateCommand {
    fn run(
        &self,
        _context: &dyn Any,
        _transport: &TransportWrapper,
    ) -> Result<Option<Box<dyn Annotate>>> {
        let private_key = EcdsaPrivateKey::new();
        let mut der_file = self.output_dir.to_owned();
        der_file.push(&self.basename);
        der_file.set_extension("der");
        private_key.save(&der_file)?;

        let public_key = private_key.public_key();
        der_file.set_extension("pub.der");
        public_key.save(&der_file)?;
        Ok(None)
    }
}

/// Export public information of an ECDSA key
/// to a C header that can be used in the ROM or ROM_EXT
#[derive(Debug, Args)]
pub struct EcdsaKeyExportCommand {
    /// ECDSA public or private key file in DER format.
    der_file: PathBuf,
    /// output header file to generate.
    output_file: Option<PathBuf>,
}

impl CommandDispatch for EcdsaKeyExportCommand {
    fn run(
        &self,
        _context: &dyn Any,
        _transport: &TransportWrapper,
    ) -> Result<Option<Box<dyn Annotate>>> {
        let key = load_pub_or_priv_key(&self.der_file)?;
        let key = EcdsaRawPublicKey::try_from(&key)?;

        let output_path = match &self.output_file {
            Some(path) => path.clone(),
            None => {
                // if no output file is provided, derive the name of the file from the
                // name of the key
                let mut out_path = self.der_file.clone();
                out_path.set_extension("h");
                out_path
            }
        };
        // We try to catch the mistake of a user that specifies the key file as output,
        // which would overwrite it. This will not detect situations where there is a symlink
        // involved so this will only catch "obvious" mistakes.
        if self.der_file == output_path {
            bail!("the output file is the same as the key file, this would overwrite the key, not allowing this")
        }
        println!("exporting key to {}", output_path.display());

        let mut file = File::create(&output_path)?;
        // construct a key name from the key file name
        let keyname = self
            .der_file
            .file_name()
            .expect("this should be a valid file name since we opened the file")
            .to_string_lossy();
        let re = Regex::new(r#"(.pub)?.der$"#).unwrap();
        let keyname = re.replace_all(&keyname, "");
        let re = Regex::new(r#"[^a-zA-Z0-9]"#).unwrap();
        let keyname = re.replace_all(&keyname, "_").to_ascii_uppercase();
        // we cannot know the purpose of this key but the header guard should probably include it
        // so we add some extra text to the guard that will not compile to force the user to fix it
        let header_guard = format!("{}_H", keyname);
        // write header guard
        writeln!(&mut file, "#ifndef {}", header_guard)?;
        writeln!(&mut file, "#define {}", header_guard)?;
        writeln!(&mut file)?;
        writeln!(&mut file, "#define {} \\", keyname)?;
        writeln!(&mut file, " {{ \\")?;
        for val in key.x.as_slice().chunks(4) {
            writeln!(
                &mut file,
                "    0x{:02x}{:02x}{:02x}{:02x}, \\",
                val[3], val[2], val[1], val[0]
            )?;
        }
        for val in key.y.as_slice().chunks(4) {
            writeln!(
                &mut file,
                "    0x{:02x}{:02x}{:02x}{:02x}, \\",
                val[3], val[2], val[1], val[0]
            )?;
        }

        writeln!(&mut file, " }}")?;
        writeln!(&mut file)?;
        writeln!(&mut file, "#endif // {}", header_guard)?;

        Ok(None)
    }
}

#[derive(Debug, Subcommand, CommandDispatch)]
pub enum EcdsaKeySubcommands {
    Show(EcdsaKeyShowCommand),
    Generate(EcdsaKeyGenerateCommand),
    Export(EcdsaKeyExportCommand),
}

#[derive(serde::Serialize, Annotate)]
pub struct EcdsaSignResult {
    #[serde(with = "serde_bytes")]
    #[annotate(format = hexstr)]
    pub digest: Vec<u8>,
    #[serde(with = "serde_bytes")]
    #[annotate(format = hexstr)]
    pub signature: Vec<u8>,
}

#[derive(Debug, Args)]
pub struct EcdsaSignCommand {
    /// File containing a SHA256 digest.
    #[arg(short, long)]
    input: Option<PathBuf>,
    /// File name to write the signature to.
    #[arg(short, long)]
    output: Option<PathBuf>,

    /// ECDSA private key file in PKCS#1 DER format.
    #[arg(value_name = "DER_FILE")]
    private_key: PathBuf,
    /// SHA256 digest of the message.
    #[arg(
        value_name = "SHA256_DIGEST",
        value_parser = Sha256Digest::from_str,
        required_unless_present = "input"
    )]
    digest: Option<Sha256Digest>,
}

impl CommandDispatch for EcdsaSignCommand {
    fn run(
        &self,
        _context: &dyn Any,
        _transport: &TransportWrapper,
    ) -> Result<Option<Box<dyn Annotate>>> {
        let private_key = EcdsaPrivateKey::load(&self.private_key)?;
        let digest = if let Some(input) = &self.input {
            let bytes = std::fs::read(input)?;
            Sha256Digest::from_le_bytes(bytes)?
        } else {
            self.digest.clone().unwrap()
        };
        let signature = private_key.sign(&digest)?.to_vec()?;
        if let Some(output) = &self.output {
            std::fs::write(output, &signature)?;
        }
        Ok(Some(Box::new(EcdsaSignResult {
            digest: digest.to_le_bytes(),
            signature,
        })))
    }
}

#[derive(Debug, Args)]
pub struct EcdsaVerifyCommand {
    /// Key file in DER format.
    #[arg(value_name = "KEY")]
    der_file: PathBuf,
    /// SHA256 digest of the message as a hex string (big-endian), i.e. 0x...
    #[arg(value_name = "SHA256_DIGEST")]
    digest: String,
    /// Signature to be verified as a hex string.
    signature: String,
}

impl CommandDispatch for EcdsaVerifyCommand {
    fn run(
        &self,
        _context: &dyn Any,
        _transport: &TransportWrapper,
    ) -> Result<Option<Box<dyn Annotate>>> {
        let key = load_pub_or_priv_key(&self.der_file)?;
        let digest = Sha256Digest::from_str(&self.digest)?;
        let signature = EcdsaRawSignature::try_from(hex::decode(&self.signature)?.as_slice())?;
        key.verify(&digest, &signature)?;
        Ok(None)
    }
}

#[derive(Debug, Subcommand, CommandDispatch)]
/// ECDSA commands.
pub enum Ecdsa {
    #[command(subcommand)]
    Key(EcdsaKeySubcommands),
    Sign(EcdsaSignCommand),
    Verify(EcdsaVerifyCommand),
}
