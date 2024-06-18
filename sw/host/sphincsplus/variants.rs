// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use crate::SpxError;
use paste::paste;
use strum::{Display, EnumString};

// The `algorithms` macro provides a uniform interface to the underlying C
// library.
macro_rules! algorithms {
    (
        $(#[$outer:meta])*
        $vis:vis enum $Enum:ident {
            $(
                $(#[$inner:meta])*
                $enumerator:ident => $stem:ident,
            )*
        }
    ) => {
        $(#[$outer])*
        #[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
        $vis enum $Enum {
            $(
                $(#[$inner])*
                $enumerator,
            )*
        }

        paste! {
            #[allow(dead_code)]
            impl $Enum {
                pub(crate) fn public_key_len(&self) -> usize {
                    match *self {
                    $(
                        $Enum::$enumerator => [<bindgen_ $stem>]::CRYPTO_PUBLICKEYBYTES as usize
                    ),*
                    }
                }
                pub(crate) fn secret_key_len(&self) -> usize {
                    match *self {
                    $(
                        $Enum::$enumerator => [<bindgen_ $stem>]::CRYPTO_SECRETKEYBYTES as usize
                    ),*
                    }
                }
                pub(crate) fn seed_len(&self) -> usize {
                    match *self {
                    $(
                        $Enum::$enumerator => [<bindgen_ $stem>]::CRYPTO_SEEDBYTES as usize
                    ),*
                    }
                }
                pub(crate) fn signature_len(&self) -> usize {
                    match *self {
                    $(
                        $Enum::$enumerator => [<bindgen_ $stem>]::CRYPTO_BYTES as usize
                    ),*
                    }
                }

                pub(crate) fn keypair_from_seed(&self, seed: &[u8]) -> Result<(Vec<u8>, Vec<u8>), SpxError> {
                    if seed.len() != self.seed_len() {
                        return Err(SpxError::BadSeedLength(seed.len()));
                    }
                    let mut pk = vec![0u8; self.public_key_len()];
                    let mut sk = vec![0u8; self.secret_key_len()];
                    // SAFETY: the buffers are sized to the algorithm variant's requirements.
                    let err_code = unsafe {
                        match *self {
                        $(
                            $Enum::$enumerator => [<bindgen_ $stem>]::[<SPX_ $stem _crypto_sign_seed_keypair>](
                                pk.as_mut_ptr(),
                                sk.as_mut_ptr(),
                                seed.as_ptr(),
                            )
                        ),*
                        }
                    };
                    if err_code != 0 {
                        return Err(SpxError::KeyGen(err_code));
                    }
                    Ok((pk, sk))
                }

                pub(crate) fn keypair_generate(&self) -> Result<(Vec<u8>, Vec<u8>), SpxError> {
                    let mut pk = vec![0u8; self.public_key_len()];
                    let mut sk = vec![0u8; self.secret_key_len()];
                    // SAFETY: the buffers are sized to the algorithm variant's requirements.
                    let err_code = unsafe {
                        match *self {
                        $(
                            $Enum::$enumerator => [<bindgen_ $stem>]::[<SPX_ $stem _crypto_sign_keypair>](
                                pk.as_mut_ptr(),
                                sk.as_mut_ptr(),
                            )
                        ),*
                        }
                    };

                    if err_code != 0 {
                        return Err(SpxError::KeyGen(err_code));
                    }
                    Ok((pk, sk))
                }

                pub(crate) fn sign(&self, sk: &[u8], msg: &[u8]) -> Result<Vec<u8>, SpxError> {
                    if sk.len() != self.secret_key_len() {
                        return Err(SpxError::BadKeyLength(sk.len()));
                    }
                    let mut signature = vec![0u8; self.signature_len()];
                    let mut bytes_written = 0;
                    // SAFETY: the secret key buffer is checked to meet the variant's
                    // requirments.  The signature buffer is created to meet the variant's
                    // requirements.  The message is passed to the underlying function with its length.
                    let err_code = unsafe {
                        match *self {
                        $(
                            $Enum::$enumerator => [<bindgen_ $stem>]::[<SPX_ $stem _crypto_sign_signature>](
                                signature.as_mut_ptr(),
                                &mut bytes_written,
                                msg.as_ptr(),
                                msg.len(),
                                sk.as_ptr(),
                            )
                        ),*
                        }
                    };
                    if err_code != 0 {
                        return Err(SpxError::SigGen(err_code));
                    }
                    if bytes_written != signature.len() {
                        return Err(SpxError::BadSigLength(bytes_written));
                    }
                    Ok(signature)
                }

                pub(crate) fn verify(&self, pk: &[u8], signature: &[u8], msg: &[u8]) -> Result<(), SpxError> {
                    if pk.len() != self.public_key_len() {
                        return Err(SpxError::BadKeyLength(pk.len()));
                    }
                    if signature.len() != self.signature_len() {
                        return Err(SpxError::BadSigLength(signature.len()));
                    }
                    // SAFETY: the public key buffer is checked to meet the variant's
                    // requirments.  The signature buffer is checked to meet the variant's
                    // requirements.  The message is passed to the underlying function with its length.
                    let err_code = unsafe {
                        match *self {
                        $(
                            $Enum::$enumerator => [<bindgen_ $stem>]::[<SPX_ $stem _crypto_sign_verify>](
                                signature.as_ptr(),
                                signature.len(),
                                msg.as_ptr(),
                                msg.len(),
                                pk.as_ptr(),
                            )
                        ),*
                        }
                    };
                    if err_code != 0 {
                        return Err(SpxError::BadSignature);
                    }
                    Ok(())
                }
            } // end impl

            $(
                #[cfg(test)]
                mod [<test_ $stem>] {
                    use super::*;

                    const ALGO: SphincsPlus = SphincsPlus::$enumerator;

                    #[test]
                    fn keypair_different_seeds_test() {
                        // Generate keypairs from two different seeds and check that the values are not equal.
                        let seed1 = vec![255u8; ALGO.seed_len()];
                        let (pk1, sk1) = ALGO.keypair_from_seed(&seed1).unwrap();
                        let seed2 = vec![0; ALGO.seed_len()];
                        let (pk2, sk2) = ALGO.keypair_from_seed(&seed2).unwrap();
                        assert_ne!(pk1, pk2);
                        assert_ne!(sk1, sk2);
                    }

                    #[test]
                    fn keypair_same_seed_test() {
                        // Generate keypairs from the same seed and check that the values are equal.
                        let seed = vec![255u8; ALGO.seed_len()];
                        let (pk1, sk1) = ALGO.keypair_from_seed(&seed).unwrap();
                        let (pk2, sk2) = ALGO.keypair_from_seed(&seed).unwrap();
                        assert_eq!(pk1, pk2);
                        assert_eq!(sk1, sk2);
                    }

                    #[test]
                    fn random_keypair_test() {
                        // Generate two random keypairs and check that they are not equal.
                        let (pk1, sk1) = ALGO.keypair_generate().unwrap();
                        let (pk2, sk2) = ALGO.keypair_generate().unwrap();
                        assert_ne!(pk1, pk2);
                        assert_ne!(sk1, sk2);
                    }

                    #[test]
                    fn sign_verify_test() {
                        // Check that a generated signature passes verification.
                        let (pk, sk) = ALGO.keypair_generate().unwrap();
                        let msg: Vec<u8> = vec![255u8; 100];
                        let mut sig = ALGO.sign(&sk, &msg).unwrap();
                        assert!(ALGO.verify(&pk, &sig, &msg).is_ok());

                        // Check that manipulating the signature causes it to fail verification.
                        sig[0] ^= 0xff;
                        let verification_result = ALGO.verify(&pk, &sig, &msg);
                        assert!(verification_result.is_err());
                        assert_eq!(
                            verification_result.unwrap_err().to_string(),
                            SpxError::BadSignature.to_string()
                        );
                    }
                }
            )*
        } // end paste
    };
}

// NOTE: The algorithm variant "stem" (the word after `=>`) needs to correspond to
// the bindgen library name and `NAMESPACE` preprocessor symbol used to construct
// that libarary.
algorithms! {
    #[derive(EnumString, Display)]
    #[strum(ascii_case_insensitive)]
    pub enum SphincsPlus {
        #[strum(serialize="SPHINCS+-SHAKE-128s-simple", serialize="SHAKE-128s-simple")]
        Shake128sSimple => shake_128s_simple,
        #[strum(serialize="SPHINCS+-SHA2-128s-simple", serialize="SHA2-128s-simple")]
        Sha2128sSimple => sha2_128s_simple,
    }
}
