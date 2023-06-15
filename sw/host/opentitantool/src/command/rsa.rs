// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::{bail, Result};
use clap::{Args, Subcommand};
use regex::Regex;
use serde_annotate::Annotate;
use std::any::Any;
use std::fs::File;
use std::io::Write;
use std::path::PathBuf;

use opentitanlib::app::command::CommandDispatch;
use opentitanlib::app::TransportWrapper;
use opentitanlib::crypto::rsa::{
    Exponent, Modulus, N0Inv, RsaPrivateKey, RsaPublicKey, Signature, RR,
};
use opentitanlib::crypto::sha256::Sha256Digest;
use opentitanlib::util::parse_int::ParseInt;

/// Given the path to a public key, returns the public key. Given
/// the path to a private key, extracts the public key from the private
/// key and returns the public key.
fn load_pub_or_priv_key(path: &PathBuf) -> Result<RsaPublicKey> {
    if let Ok(key) = RsaPublicKey::from_pkcs1_der_file(path) {
        return Ok(key);
    }
    Ok(RsaPublicKey::from_private_key(
        &RsaPrivateKey::from_pkcs8_der_file(path)?,
    ))
}

fn load_priv_key(path: &str) -> Result<RsaPrivateKey> {
    RsaPrivateKey::from_pkcs8_der_file(path)
}

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
#[derive(Debug, Args)]
pub struct RsaKeyShowCommand {
    #[arg(
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
        let key = load_pub_or_priv_key(&self.der_file)?;

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
#[derive(Debug, Args)]
pub struct RsaKeyGenerateCommand {
    #[arg(name = "OUTPUT_DIR", help = "Output directory")]
    output_dir: PathBuf,
    #[arg(name = "BASENAME", help = "Basename for the generated key pair")]
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

/// Export public information of a private or public RSA key
/// to a C header that can be used in the ROM or ROM_EXT
#[derive(Debug, Args)]
pub struct RsaKeyExportCommand {
    #[arg(
        name = "DER_FILE",
        help = "RSA public or private key file in DER format"
    )]
    der_file: PathBuf,
    #[arg(name = "OUTPUT_FILE", help = "output header file to generate")]
    output_file: Option<PathBuf>,
}

/// Write the content of a big integer as an array of 32-bit words.
/// The number must be represented as an array of bytes in little-endian whose
/// length is a multiple of four. The output is compatible with the format used
/// by the ROM and ROM_EXT with sigverify_rom_rsa_key_t, ie the modulus and n0_inv
/// are represented as an array of 32-bit words in little-endian. To make the function's
/// output flexible, the function can print up to a specified number of items per
/// line, and each line can be prefixed and suffixed with a specified string
fn write_bigint_as_u32<W: Write>(
    out: &mut W,
    number: Vec<u8>,
    nr_per_line: usize,
    prefix: &str,
    suffix: &str,
) -> Result<()> {
    let chunk = std::mem::size_of::<u32>();
    assert!(
        number.len() % chunk == 0,
        "the big integer size is not a multiple of 4 bytes"
    );
    for (idx, num) in number.windows(chunk).step_by(chunk).enumerate() {
        // print prefix and newline on multiples of nr_per_line
        if idx % nr_per_line == 0 {
            if idx != 0 {
                writeln!(out, "{}", suffix)?;
            }
            write!(out, "{}", prefix)?;
        }
        // print one 32-bit word
        let val = u32::from_le_bytes(num.try_into().unwrap());
        write!(out, "{:#010x}, ", val)?;
    }
    // extra return to the line
    writeln!(out, "{}", suffix)?;
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use anyhow::Result;

    #[test]
    fn test_write_bigint_as_u32() -> Result<()> {
        let mut buf: Vec<u8> = Vec::new();
        let bignum = vec![
            0x10, 0x32, 0x54, 0x76, 0x98, 0xba, 0xdc, 0xfe, 0x18, 0x29, 0x3a, 0x4b,
        ];
        write_bigint_as_u32(&mut buf, bignum, 2, "X", "Y")?;
        let output = br#"X0x76543210, 0xfedcba98, Y
X0x4b3a2918, Y
"#;
        assert_eq!(buf, output);
        Ok(())
    }
}

impl CommandDispatch for RsaKeyExportCommand {
    fn run(
        &self,
        _context: &dyn Any,
        _transport: &TransportWrapper,
    ) -> Result<Option<Box<dyn Annotate>>> {
        let key = load_pub_or_priv_key(&self.der_file)?;

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
        writeln!(&mut file, "    .n = \\")?;
        writeln!(&mut file, "        {{{{ \\")?;
        write_bigint_as_u32(
            &mut file,
            key.modulus().to_le_bytes(),
            5,
            "            ",
            "\\",
        )?;
        writeln!(&mut file, "        }}}}, \\")?;
        writeln!(&mut file, "    .n0_inv = {{ \\")?;
        write_bigint_as_u32(&mut file, key.n0_inv()?.to_le_bytes(), 4, "        ", "\\")?;
        writeln!(&mut file, "        }}, \\")?;
        writeln!(&mut file, " }}")?;
        writeln!(&mut file)?;
        writeln!(&mut file, "#endif // {}", header_guard)?;

        Ok(None)
    }
}

#[derive(Debug, Subcommand, CommandDispatch)]
pub enum RsaKeySubcommands {
    Show(RsaKeyShowCommand),
    Generate(RsaKeyGenerateCommand),
    Export(RsaKeyExportCommand),
}

#[derive(serde::Serialize)]
pub struct RsaSignResult {
    pub digest: String,
    pub signature: String,
}

#[derive(Debug, Args)]
pub struct RsaSignCommand {
    #[arg(short, long, help = "File containing a SHA256 digest")]
    input: Option<PathBuf>,
    #[arg(short, long, help = "File name to write the signature to")]
    output: Option<PathBuf>,

    #[arg(
        name = "DER_FILE",
        value_parser = load_priv_key,
        help = "RSA private key file in PKCS#1 DER format"
    )]
    private_key: RsaPrivateKey,
    #[arg(
        name = "SHA256_DIGEST",
        value_parser = Sha256Digest::from_str,
        required_unless_present = "input",
        help = "SHA256 digest of the message"
    )]
    digest: Option<Sha256Digest>,
}

impl CommandDispatch for RsaSignCommand {
    fn run(
        &self,
        _context: &dyn Any,
        _transport: &TransportWrapper,
    ) -> Result<Option<Box<dyn Annotate>>> {
        let digest = if let Some(input) = &self.input {
            let bytes = std::fs::read(input)?;
            Sha256Digest::from_le_bytes(bytes)?
        } else {
            self.digest.clone().unwrap()
        };
        let signature = self.private_key.sign(&digest)?;
        if let Some(output) = &self.output {
            signature.write_to_file(output)?;
        }
        Ok(Some(Box::new(RsaSignResult {
            digest: digest.to_string(),
            signature: signature.to_string(),
        })))
    }
}

#[derive(Debug, Args)]
pub struct RsaVerifyCommand {
    #[arg(name = "KEY", help = "Key file in DER format")]
    der_file: PathBuf,
    #[arg(
        name = "SHA256_DIGEST",
        help = "SHA256 digest of the message as a hex string (big-endian), i.e. 0x..."
    )]
    digest: String,
    #[arg(
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

#[derive(Debug, Subcommand, CommandDispatch)]
/// RSA commands.
#[allow(clippy::large_enum_variant)]
pub enum Rsa {
    #[command(subcommand)]
    Key(RsaKeySubcommands),
    Sign(RsaSignCommand),
    Verify(RsaVerifyCommand),
}
