//! This module contains the Endpoint Encryption Keys (EEK) utilities for encrypting
//! factory payloads for CSR versions 1 & 2. EEK usage was dropped for CSR v3.
//!
//! NOTE: Since CSR version 3 drops the encryption requirement, Google is publishing
//! the private Google EEKs so that testing on platforms that support CSR versions
//! 1 & 2 have diagnostic parity with CSR v3 systems.

use anyhow::{bail, Context, Result};
use coset::{CborSerializable, CoseKdfContextBuilder, Nonce, PartyInfo, SuppPubInfoBuilder};
use openssl::{
    bn::{BigNum, BigNumContext},
    derive::Deriver,
    ec::{EcGroup, EcKey, EcPoint, PointConversionForm},
    md::Md,
    nid::Nid,
    pkey::{HasPublic, Id, PKey, PKeyRef, Private, Public},
    pkey_ctx::PkeyCtx,
};

pub const X25519_EEK_ID: &[u8] = b"\xd0\xae\xc1\x15\xca\x2a\xcf\x73\xae\x6b\xcc\xcb\xd1\x96\x1d\x65\xe8\xb1\xdd\xd7\x4a\x1a\x37\xb9\x43\x3a\x97\xd5\x99\xdf\x98\x08";
// X25519_EEK_PUBLIC_X: b"\xbe\x85\xe7\x46\xc4\xa3\x42\x5a\x40\xd9\x36\x3a\xa6\x15\xd0\x2c\x58\x7e\x3d\xdc\x33\x02\x32\xd2\xfc\x5e\x1e\x87\x25\x5f\x72\x60";
pub const X25519_EEK_PRIVATE: &[u8] = b"\x47\x66\x65\xdb\xaa\xe1\x1d\xdb\xd3\x03\xf7\xad\x68\xbb\xff\x8d\x90\xaf\x8a\x4f\xb8\xbf\x7c\xf3\x39\xc7\xe9\x73\xec\x70\x75\x8c";

pub const P256_EEK_ID: &[u8] = b"\x35\x73\xb7\x3f\xa0\x8a\x80\x89\xb1\x26\x67\xe9\xcb\x7c\x75\xa1\xaf\x02\x61\xfc\x6e\x65\x03\x91\x3b\xd3\x4b\x7d\x14\x94\x3e\x46";
pub const P256_EEK_PUBLIC_X: &[u8] = b"\xe0\x41\xcf\x2f\x0f\x34\x0f\x1c\x33\x2c\x41\xb0\xcf\xd7\x0c\x30\x55\x35\xd2\x1e\x6a\x47\x13\x4b\x2e\xd1\x48\x96\x7e\x24\x9c\x68";
pub const P256_EEK_PUBLIC_Y: &[u8] = b"\x1f\xce\x45\xc5\xfb\x61\xba\x81\x21\xf9\xe5\x05\x9b\x9b\x39\x0e\x76\x86\x86\x47\xb8\x1e\x2f\x45\xf1\xce\xaf\xda\x3f\x80\x68\xdb";
pub const P256_EEK_PRIVATE: &[u8] = b"\x00\xd1\x0a\x51\x59\xb2\xa0\x39\x43\xc8\x58\xf1\xdc\x3f\xc4\x0a\x03\x39\x31\x9d\x34\x01\x8f\x30\xa9\xc4\x46\x7e\x64\x61\x35\x6d\xdf";

/// Get the well-known P256 GEEK private key.
pub fn p256_geek() -> PKey<Private> {
    let p256 = EcGroup::from_curve_name(Nid::X9_62_PRIME256V1).unwrap();
    let private = BigNum::from_slice(P256_EEK_PRIVATE).unwrap();
    let mut public_key = EcPoint::new(&p256).unwrap();
    public_key
        .set_affine_coordinates_gfp(
            &p256,
            &BigNum::from_slice(P256_EEK_PUBLIC_X).unwrap(),
            &BigNum::from_slice(P256_EEK_PUBLIC_Y).unwrap(),
            &mut BigNumContext::new().unwrap(),
        )
        .unwrap();

    let ec_key = EcKey::from_private_components(&p256, &private, &public_key).unwrap();
    PKey::from_ec_key(ec_key).unwrap()
}

/// Get the well-known X25519 GEEK private key.
pub fn x25519_geek() -> PKey<Private> {
    PKey::private_key_from_raw_bytes(X25519_EEK_PRIVATE, Id::X25519).unwrap()
}

pub fn derive_ephemeral_symmetric_key(
    private: &PKeyRef<Private>,
    public: &PKeyRef<Public>,
) -> Result<[u8; 32]> {
    let mut deriver = Deriver::new(private)?;
    deriver.set_peer(public)?;
    let shared_secret = deriver.derive_to_vec()?;

    let supp_pub_info = SuppPubInfoBuilder::new().key_data_length(256).build();

    let context = CoseKdfContextBuilder::new()
        .algorithm(coset::iana::Algorithm::A256GCM)
        .party_u_info(kdf_party_info(b"client", public)?)
        .party_v_info(kdf_party_info(b"server", private)?)
        .supp_pub_info(supp_pub_info)
        .build();
    let hkdf_info = match context.to_vec() {
        Ok(v) => v,
        Err(e) => bail!("Error serializing COSE_KDF_Context: {e}"),
    };

    let mut kdf = PkeyCtx::new_id(Id::HKDF)?;
    kdf.derive_init()?;
    kdf.set_hkdf_key(&shared_secret)?;
    kdf.set_hkdf_md(Md::sha256())?;
    kdf.add_hkdf_info(&hkdf_info)?;

    let mut derived_key = [0; 32];
    kdf.derive(Some(&mut derived_key))?;
    Ok(derived_key)
}

fn kdf_party_info<T: HasPublic>(identity: &[u8], key: &PKeyRef<T>) -> Result<PartyInfo> {
    Ok(PartyInfo {
        identity: Some(identity.to_vec()),
        nonce: Some(Nonce::Bytes(vec![])),
        other: Some(raw_key_bytes(key)?),
    })
}

fn raw_key_bytes<T: HasPublic>(key: &PKeyRef<T>) -> Result<Vec<u8>> {
    match key.id() {
        Id::X25519 => key.raw_public_key().context("Unable to fetch raw public key"),
        Id::EC => {
            let ec = key.ec_key()?;
            let mut ctx = BigNumContext::new()?;
            let mut uncompressed = ec.public_key().to_bytes(
                ec.group(),
                PointConversionForm::UNCOMPRESSED,
                &mut ctx,
            )?;
            // uncompressed format is '04 | X | Y'. For KDF purposes, we just want 'X | Y'
            uncompressed.remove(0);
            Ok(uncompressed)
        }
        other => bail!("Unsupported public key type {other:?}"),
    }
}
