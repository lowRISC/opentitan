use crate::cbor::field_value::FieldValue;
use crate::cbor::value_from_bytes;
use crate::dice::ChainForm;
use crate::eek;
use crate::publickey::{KeyAgreementPublicKey, PublicKey};
use crate::rkp::{ProtectedData, UdsCerts, UdsCertsEntry};
use crate::session::Session;
use anyhow::{anyhow, bail, Context, Result};
use ciborium::value::Value;
use coset::{iana, Algorithm, AsCborValue, CoseEncrypt, CoseKey, CoseRecipient, CoseSign1, Label};
use openssl::cipher::Cipher;
use openssl::cipher_ctx::CipherCtx;
use openssl::pkey::{Id, PKey, Private};

const COSE_RECIPIENT_PUBKEY_LABEL: i64 = -1;

impl ProtectedData {
    pub(crate) fn from_cose_encrypt(
        session: &Session,
        protected_data: CoseEncrypt,
        challenge: &[u8],
        verified_device_info: &Value,
        tag: &[u8],
    ) -> Result<ProtectedData> {
        let (recipient, eek) = Self::match_recipient(&protected_data.recipients)?;

        let mut headers = recipient.unprotected.rest;
        let pubkey_index = headers
            .iter()
            .position(|p| p.0 == Label::Int(COSE_RECIPIENT_PUBKEY_LABEL))
            .context("Unable to locate public key in COSE_encrypt recipients.")?;
        let mut pubkey_cose = match CoseKey::from_cbor_value(headers.remove(pubkey_index).1) {
            Ok(key) => key,
            Err(e) => bail!("Error converting CBOR into COSE_key: {:?}", e),
        };

        Self::work_around_recipient_key_missing_alg(&mut pubkey_cose, &eek)?;

        let pubkey = KeyAgreementPublicKey::from_cose_key(&pubkey_cose)?;
        let encryption_key = eek::derive_ephemeral_symmetric_key(&eek, pubkey.pkey())
            .with_context(|| format!("for pubkey {:?}", pubkey_cose))?;

        let protected_data_plaintext = protected_data
            .decrypt(&[], |ciphertext, aad| {
                let (ciphertext, tag) = ciphertext.split_at(ciphertext.len() - 16);
                let mut plaintext = Vec::new();
                let mut ctx = CipherCtx::new().context("Unable to load cipher context")?;
                // decrypt_init must be called twice because our IV is not 12 bytes, which is what
                // AES-GCM wants by default. The first init tells openssl the cipher+mode, then we
                // can tell openssl the IV len, and only after that can we set the non-standard IV.
                ctx.decrypt_init(Some(Cipher::aes_256_gcm()), Some(&encryption_key), None)?;
                ctx.set_iv_length(protected_data.unprotected.iv.len())?;
                ctx.decrypt_init(None, None, Some(&protected_data.unprotected.iv))?;
                ctx.set_tag(tag)?;
                ctx.cipher_update(aad, None).context("Error setting AAD on cipher")?;
                ctx.cipher_update_vec(ciphertext, &mut plaintext)
                    .context("Error decrypting ciphertext")?;
                ctx.cipher_final_vec(&mut plaintext).context("Error finalizing decryption")?;
                Ok::<Vec<u8>, anyhow::Error>(plaintext)
            })
            .context("while decrypting ProtectedData")?;

        Self::from_cbor_bytes(
            session,
            &protected_data_plaintext,
            challenge,
            verified_device_info,
            tag,
        )
    }

    fn from_cbor_bytes(
        session: &Session,
        plaintext_cbor: &[u8],
        challenge: &[u8],
        verified_device_info: &Value,
        tag: &[u8],
    ) -> Result<Self> {
        let mut array = match value_from_bytes(plaintext_cbor) {
            Ok(Value::Array(a)) => a,
            Ok(other) => bail!("Expected array for ProtectedDataPayload, found {other:?}"),
            Err(e) => bail!(
                "Error '{e:?}' parsing ProtectedDataPayload '{}'",
                hex::encode(plaintext_cbor)
            ),
        };

        if array.len() != 2 && array.len() != 3 {
            bail!("ProtectedDataPayload size must be 2 or 3, found {array:?}");
        }

        // pull items out in reverse order to avoid shifting the vector
        let uds_certs = if array.len() != 3 {
            None
        } else {
            let uds_certs_field = FieldValue::from_optional_value("UdsCerts", array.pop());
            Self::to_uds_certs(uds_certs_field.into_map()?)?
        };

        let dice_chain =
            Value::Array(FieldValue::from_optional_value("DiceChain", array.pop()).into_array()?);
        let dice_chain = ChainForm::from_value(session, dice_chain)?;

        let mac_key = Self::validate_mac_key(
            challenge,
            verified_device_info,
            tag,
            FieldValue::from_optional_value("SignedMac", array.pop()).into_cose_sign1()?,
            dice_chain.leaf_public_key(),
        )?;

        Ok(ProtectedData::new(mac_key, dice_chain, uds_certs))
    }

    fn validate_mac_key(
        challenge: &[u8],
        verified_device_info: &Value,
        tag: &[u8],
        signed_mac: CoseSign1,
        signer: &PublicKey,
    ) -> Result<Vec<u8>> {
        let mut aad: Vec<u8> = vec![];
        ciborium::ser::into_writer(
            // This can be optimized if/when ciborium exposes lower-level serialization routines
            &Value::Array(vec![
                Value::Bytes(challenge.to_vec()),
                verified_device_info.clone(),
                Value::Bytes(tag.to_vec()),
            ]),
            &mut aad,
        )?;
        signer.verify_cose_sign1(&signed_mac, &aad).context("verifying signed MAC")?;
        signed_mac.payload.ok_or(anyhow!("SignedMac is missing the payload"))
    }

    fn to_uds_certs(kv_pairs: Vec<(Value, Value)>) -> Result<Option<UdsCerts>> {
        if kv_pairs.is_empty() {
            return Ok(None);
        }

        let mut uds_certs = UdsCerts::new();
        for pair in kv_pairs {
            match pair {
                (Value::Text(signer), value) => uds_certs.add_signer(signer, value)?,
                (k, v) => bail!("Expected (string, value), but found ({k:?}, {v:?}"),
            }
        }
        Ok(Some(uds_certs))
    }

    fn work_around_recipient_key_missing_alg(
        cose_key: &mut CoseKey,
        eek: &PKey<Private>,
    ) -> Result<()> {
        let cose_alg = match eek.id() {
            Id::X25519 => iana::Algorithm::ECDH_ES_HKDF_256,
            Id::EC if eek.bits() == 256 => iana::Algorithm::ES256,
            other => bail!("Unsupported EEK: {:?}, key size: {}", other, eek.bits()),
        };

        match &cose_key.alg {
            None => cose_key.alg = Some(Algorithm::Assigned(cose_alg)),
            Some(Algorithm::Assigned(alg)) if *alg == cose_alg => (),
            Some(Algorithm::Assigned(alg)) => {
                bail!("Algorithm mismatch between EEK ({cose_alg:?}) and recipient ({alg:?})")
            }
            other => bail!("COSE_Encrypt recipient pubkey has unexpected algorithm: {other:?}"),
        }
        Ok(())
    }

    /// Look through a set of COSE_recipients to see if any of them match a known EEK. If so,V
    /// return the matching recipieint and EEK to the caller so they can perform key agreement.
    fn match_recipient(recipients: &Vec<CoseRecipient>) -> Result<(CoseRecipient, PKey<Private>)> {
        for r in recipients {
            if r.unprotected.key_id == eek::X25519_EEK_ID {
                return Ok((r.clone(), eek::x25519_geek()));
            } else if r.unprotected.key_id == eek::P256_EEK_ID {
                return Ok((r.clone(), eek::p256_geek()));
            }
        }
        Err(anyhow!("Unable to locate a COSE_recipient matching any known EEK"))
    }
}

impl UdsCerts {
    pub fn add_signer(&mut self, signer: String, data: Value) -> Result<()> {
        // For now, assume all signers are using x.509 certs. This may change in the future for
        // platforms that need custom certification mechanisms for UDS_pub.
        match self.0.get_mut(&signer) {
            Some(_) => bail!("Signer '{signer}' entry found twice in the UdsCerts"),
            None => self.0.insert(signer, UdsCertsEntry::from_cbor_value(data)?),
        };
        Ok(())
    }
}

impl UdsCertsEntry {
    fn from_cbor_value(data: Value) -> Result<Self> {
        match data {
            Value::Array(certs) => {
                let mut cert_buffers = vec![];
                for cert in certs {
                    match cert {
                        Value::Bytes(b) => cert_buffers.push(b),
                        other => bail!("Expected UDS cert byte array found '{other:?}'"),
                    }
                }
                UdsCertsEntry::new_x509_chain(cert_buffers)
            }
            other => Err(anyhow!("Expected CBOR array of certificates, found {other:?}")),
        }
    }
}
