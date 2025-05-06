// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::Result;
use libloading::Library;
use sphincsplus::SpxDomain;
use std::ffi::{CStr, CString};
use thiserror::Error;

use crate::{GenerateFlags, KeyEntry, KeyInfo, SpxInterface};

#[derive(Error, Debug)]
pub enum AcornError {
    #[error("acorn library error: {0}")]
    Message(String),
}

/// Converts a C-string into a rust string.
///
/// # Safety
///
/// `ptr` should either be a null pointer or a valid pointer to a C NUL-terminated string.
unsafe fn rust_string(ptr: *const std::ffi::c_char) -> String {
    if ptr.is_null() {
        "nullptr for string!".into()
    } else {
        // SAFETY: `ptr` is a valid pointer to a C string.
        unsafe { CStr::from_ptr(ptr) }
            .to_string_lossy()
            .into_owned()
    }
}

#[allow(non_snake_case)]
#[allow(dead_code)]
struct FreeFunc {
    getVersion: acorn_bindgen::acorn_free_getVersion,
    list: acorn_bindgen::acorn_free_list,
    getPublic: acorn_bindgen::acorn_free_getPublic,
    getPublicHash: acorn_bindgen::acorn_free_getPublicHash,
    getKeyInfo: acorn_bindgen::acorn_free_getKeyInfo,
    generate: acorn_bindgen::acorn_free_generate,
    importKeypair: acorn_bindgen::acorn_free_importKeypair,
    sign: acorn_bindgen::acorn_free_sign,
    verify: acorn_bindgen::acorn_free_verify,
    signImmediate: acorn_bindgen::acorn_free_signImmediate,
    verifyImmediate: acorn_bindgen::acorn_free_verifyImmediate,
    see_getVersion: acorn_bindgen::acorn_free_see_getVersion,
}

struct AcornLibrary {
    _library: libloading::Library,
    func: acorn_bindgen::acorn_cmdlist,
    free: FreeFunc,
}

impl AcornLibrary {
    pub fn new<P>(path: P) -> Result<Self>
    where
        P: AsRef<std::ffi::OsStr>,
    {
        // SAFETY: The calls to Library::get specify the correct type of
        // the named symbol.
        unsafe {
            let library = Library::new(path)?;
            let getcmdlist: acorn_bindgen::acorn_getcmdlist =
                library.get(b"acorn_getcmdlist\0").map(|sym| Some(*sym))?;

            let mut func = acorn_bindgen::acorn_cmdlist::default();
            let mut err = std::ptr::null_mut::<std::ffi::c_char>();
            let ret = (getcmdlist.expect("getcmdlist"))(&mut func, &mut err);
            if ret != 0 {
                return Err(AcornError::Message(rust_string(err)).into());
            }
            let free = FreeFunc {
                getVersion: library
                    .get(b"acorn_free_getVersion\0")
                    .map(|sym| Some(*sym))?,
                list: library.get(b"acorn_free_list\0").map(|sym| Some(*sym))?,
                getPublic: library
                    .get(b"acorn_free_getPublic\0")
                    .map(|sym| Some(*sym))?,
                getPublicHash: library
                    .get(b"acorn_free_getPublicHash\0")
                    .map(|sym| Some(*sym))?,
                getKeyInfo: library
                    .get(b"acorn_free_getKeyInfo\0")
                    .map(|sym| Some(*sym))?,
                generate: library
                    .get(b"acorn_free_generate\0")
                    .map(|sym| Some(*sym))?,
                importKeypair: library
                    .get(b"acorn_free_importKeypair\0")
                    .map(|sym| Some(*sym))?,
                sign: library.get(b"acorn_free_sign\0").map(|sym| Some(*sym))?,
                verify: library.get(b"acorn_free_verify\0").map(|sym| Some(*sym))?,
                signImmediate: library
                    .get(b"acorn_free_signImmediate\0")
                    .map(|sym| Some(*sym))?,
                verifyImmediate: library
                    .get(b"acorn_free_verifyImmediate\0")
                    .map(|sym| Some(*sym))?,
                see_getVersion: library
                    .get(b"acorn_free_see_getVersion\0")
                    .map(|sym| Some(*sym))?,
            };

            Ok(Self {
                _library: library,
                func,
                free,
            })
        }
    }
}

pub struct Acorn {
    lib: AcornLibrary,
}

impl Acorn {
    pub fn new<P>(path: P) -> Result<Box<Self>>
    where
        P: AsRef<std::ffi::OsStr>,
    {
        let lib = AcornLibrary::new(path)?;
        Ok(Box::new(Acorn { lib }))
    }

    /// Get the version of the acorn host software.
    pub fn get_host_version(&self) -> Result<String> {
        let mut rsp = acorn_bindgen::acorn_response_getVersion::default();
        let mut err = std::ptr::null_mut::<std::ffi::c_char>();
        // SAFETY: The arguments to `getVersion` are of the correct type.
        unsafe {
            let result = if (self.lib.func.getVersion.as_ref().expect("func.getVersion"))(
                &mut rsp, &mut err,
            ) == 0
            {
                Ok(rust_string(rsp.version))
            } else {
                Err(AcornError::Message(rust_string(err)).into())
            };
            (self.lib.free.getVersion.as_ref().expect("free.getVersion"))(
                std::ptr::null_mut(),
                &mut rsp,
            );
            result
        }
    }

    /// Get the version of the acorn module running in the HSM's secure execution environment.
    pub fn get_see_version(&self) -> Result<String> {
        let mut req = acorn_bindgen::acorn_request_see_getVersion::default();
        let mut rsp = acorn_bindgen::acorn_response_see_getVersion::default();
        let mut err = std::ptr::null_mut::<std::ffi::c_char>();
        // SAFETY: The arguments to `see_getVersion` are of the correct type.
        unsafe {
            let result = if (self
                .lib
                .func
                .see_getVersion
                .as_ref()
                .expect("func.see_getVersion"))(
                &mut req, &mut rsp, &mut err
            ) == 0
            {
                Ok(rust_string(rsp.version))
            } else {
                Err(AcornError::Message(rust_string(err)).into())
            };
            (self
                .lib
                .free
                .see_getVersion
                .as_ref()
                .expect("free.see_getVersion"))(std::ptr::null_mut(), &mut rsp);
            result
        }
    }

    // TODO: get_public_key, but get_key_info provides the same data.
    pub fn get_public_key(&self, alias: &str) -> Result<Vec<u8>> {
        let alias = CString::new(alias)?;
        // SAFETY: The data returned by `get_public_key` is copied into a rust Vec.
        // The memory allocated by the acorn library is freed by the acorn library's
        // free function.
        unsafe {
            let mut rsp = acorn_bindgen::acorn_response_getPublic::default();
            let mut err = std::ptr::null_mut::<std::ffi::c_char>();
            let result = if (self.lib.func.getPublic.as_ref().expect("func.getPublic"))(
                alias.as_ptr(),
                &mut rsp,
                &mut err,
            ) == 0
            {
                let pkey =
                    std::slice::from_raw_parts(rsp.publicKey.ptr, rsp.publicKey.len as usize);
                Ok(pkey.to_vec())
            } else {
                Err(AcornError::Message(rust_string(err)).into())
            };
            (self.lib.free.getPublic.as_ref().expect("free.getPublic"))(
                std::ptr::null_mut(),
                &mut rsp,
            );
            result
        }
    }

    // TODO: get_public_hash, but get_key_info provides the same data.
    pub fn get_public_hash(&self, public_key: &[u8]) -> Result<String> {
        // SAFETY: The string returned by `get_public_hash` is copied into a rust String.
        // The memory allocated by the acorn library is freed by the acorn library's
        // free function.
        unsafe {
            let public_key = acorn_bindgen::acorn_buffer {
                // The acorn API wants a mut ptr (but it wont mutate).
                ptr: public_key.as_ptr().cast_mut(),
                len: public_key.len() as u32,
            };
            let mut rsp = acorn_bindgen::acorn_response_getPublicHash::default();
            let mut err = std::ptr::null_mut::<std::ffi::c_char>();
            let result = if (self
                .lib
                .func
                .getPublicHash
                .as_ref()
                .expect("func.getPublicHash"))(
                public_key, &mut rsp, &mut err
            ) == 0
            {
                Ok(rust_string(rsp.hash))
            } else {
                Err(AcornError::Message(rust_string(err)).into())
            };
            (self
                .lib
                .free
                .getPublicHash
                .as_ref()
                .expect("free.getPublicHash"))(std::ptr::null_mut(), &mut rsp);
            result
        }
    }
}

impl SpxInterface for Acorn {
    fn get_version(&self) -> Result<String> {
        Ok(format!(
            "{} (see: {})",
            self.get_host_version()?,
            self.get_see_version()?
        ))
    }

    fn list_keys(&self) -> Result<Vec<KeyEntry>> {
        let mut rsp = acorn_bindgen::acorn_response_list::default();
        let mut err = std::ptr::null_mut::<std::ffi::c_char>();
        // SAFETY: The entries returned by `list` are copied into rust types.
        // The memory allocated by the acorn library is freed by the acorn library's
        // free function.
        unsafe {
            let result =
                if (self.lib.func.list.as_ref().expect("func.list"))(&mut rsp, &mut err) == 0 {
                    let entries = std::slice::from_raw_parts(rsp.entries, rsp.n_entries as usize);
                    let entries = entries
                        .iter()
                        .map(|e| KeyEntry {
                            alias: rust_string(e.alias),
                            hash: None,
                            algorithm: rust_string(e.algorithm),
                            ..Default::default()
                        })
                        .collect::<Vec<_>>();
                    Ok(entries)
                } else {
                    Err(AcornError::Message(rust_string(err)).into())
                };
            (self.lib.free.list.as_ref().expect("free.list"))(std::ptr::null_mut(), &mut rsp);
            result
        }
    }

    fn get_key_info(&self, alias: &str) -> Result<KeyInfo> {
        let alias = CString::new(alias)?;
        // SAFETY: The data returned by `get_key_info` are copied into rust data types.
        // The memory allocated by the acorn library is freed by the acorn library's
        // free function.
        unsafe {
            let mut rsp = acorn_bindgen::acorn_response_getKeyInfo::default();
            let mut err = std::ptr::null_mut::<std::ffi::c_char>();
            let result = if (self.lib.func.getKeyInfo.as_ref().expect("func.getKeyInfo"))(
                alias.as_ptr(),
                &mut rsp,
                &mut err,
            ) == 0
            {
                let pkey =
                    std::slice::from_raw_parts(rsp.publicKey.ptr, rsp.publicKey.len as usize);
                let blob =
                    std::slice::from_raw_parts(rsp.privateBlob.ptr, rsp.privateBlob.len as usize);
                Ok(KeyInfo {
                    hash: rust_string(rsp.hash),
                    algorithm: rust_string(rsp.algorithm),
                    domain: None,
                    public_key: pkey.to_vec(),
                    private_blob: blob.to_vec(),
                })
            } else {
                Err(AcornError::Message(rust_string(err)).into())
            };
            (self.lib.free.getKeyInfo.as_ref().expect("free.getKeyInfo"))(
                std::ptr::null_mut(),
                &mut rsp,
            );
            result
        }
    }

    fn generate_key(
        &self,
        alias: &str,
        algorithm: &str,
        _domain: SpxDomain,
        token: &str,
        flags: GenerateFlags,
    ) -> Result<KeyEntry> {
        let alias = CString::new(alias)?;
        let alg = CString::new(algorithm)?;
        let token = CString::new(token)?;
        // SAFETY: The data returned by `generate` are copied into rust data types.
        // The memory allocated by the acorn library is freed by the acorn library's
        // free function.
        unsafe {
            let mut rsp = acorn_bindgen::acorn_response_generate::default();
            let mut err = std::ptr::null_mut::<std::ffi::c_char>();
            let result = if (self.lib.func.generate.as_ref().expect("func.generate"))(
                alias.as_ptr(),
                alg.as_ptr(),
                token.as_ptr(),
                flags.bits(),
                &mut rsp,
                &mut err,
            ) == 0
            {
                let private_blob = if rsp.privateBlob.ptr.is_null() {
                    Vec::new()
                } else {
                    std::slice::from_raw_parts(rsp.privateBlob.ptr, rsp.privateBlob.len as usize)
                        .to_vec()
                };
                let private_key = if rsp.privateKey.ptr.is_null() {
                    Vec::new()
                } else {
                    std::slice::from_raw_parts(rsp.privateKey.ptr, rsp.privateKey.len as usize)
                        .to_vec()
                };
                Ok(KeyEntry {
                    alias: rust_string(rsp.alias),
                    hash: Some(rust_string(rsp.hash)),
                    algorithm: algorithm.to_string(),
                    domain: None,
                    private_blob,
                    private_key,
                })
            } else {
                Err(AcornError::Message(rust_string(err)).into())
            };
            (self.lib.free.generate.as_ref().expect("free.generate"))(
                std::ptr::null_mut(),
                &mut rsp,
            );
            result
        }
    }

    fn import_keypair(
        &self,
        alias: &str,
        algorithm: &str,
        _domain: SpxDomain,
        token: &str,
        overwrite: bool,
        public_key: &[u8],
        private_key: &[u8],
    ) -> Result<KeyEntry> {
        let alias = CString::new(alias)?;
        let alg = CString::new(algorithm)?;
        let token = CString::new(token)?;
        // SAFETY: The data returned by `importKeypair` are copied into rust data types.
        // The memory allocated by the acorn library is freed by the acorn library's
        // free function.
        unsafe {
            let public_key = acorn_bindgen::acorn_buffer {
                // The acorn API wants a mut ptr (but it wont mutate).
                ptr: public_key.as_ptr().cast_mut(),
                len: public_key.len() as u32,
            };
            let private_key = acorn_bindgen::acorn_buffer {
                // The acorn API wants a mut ptr (but it wont mutate).
                ptr: private_key.as_ptr().cast_mut(),
                len: private_key.len() as u32,
            };

            let mut rsp = acorn_bindgen::acorn_response_importKeypair::default();
            let mut err = std::ptr::null_mut::<std::ffi::c_char>();
            let result = if (self
                .lib
                .func
                .importKeypair
                .as_ref()
                .expect("func.importKeypair"))(
                alias.as_ptr(),
                alg.as_ptr(),
                public_key,
                private_key,
                token.as_ptr(),
                u32::from(overwrite),
                &mut rsp,
                &mut err,
            ) == 0
            {
                Ok(KeyEntry {
                    alias: rust_string(rsp.alias),
                    hash: Some(rust_string(rsp.hash)),
                    algorithm: algorithm.to_string(),
                    domain: None,
                    ..Default::default()
                })
            } else {
                Err(AcornError::Message(rust_string(err)).into())
            };
            (self
                .lib
                .free
                .importKeypair
                .as_ref()
                .expect("free.importKeypair"))(std::ptr::null_mut(), &mut rsp);
            result
        }
    }

    fn sign(
        &self,
        alias: Option<&str>,
        key_hash: Option<&str>,
        domain: SpxDomain,
        message: &[u8],
    ) -> Result<Vec<u8>> {
        let alias = alias.map(CString::new).transpose()?;
        let key_hash = key_hash.map(CString::new).transpose()?;
        let message = domain.prepare(message);
        // SAFETY: The signature returned by `sign` is copied into a rust Vec.
        // The memory allocated by the acorn library is freed by the acorn library's
        // free function.
        unsafe {
            let message = acorn_bindgen::acorn_buffer {
                ptr: message.as_ptr().cast_mut(),
                len: message.len() as u32,
            };
            let mut rsp = acorn_bindgen::acorn_response_sign::default();
            let mut err = std::ptr::null_mut::<std::ffi::c_char>();
            let result = if (self.lib.func.sign.as_ref().expect("func.sign"))(
                alias
                    .as_ref()
                    .map(|x| x.as_ptr())
                    .unwrap_or(std::ptr::null()),
                key_hash
                    .as_ref()
                    .map(|x| x.as_ptr())
                    .unwrap_or(std::ptr::null()),
                message,
                &mut rsp,
                &mut err,
            ) == 0
            {
                let signature =
                    std::slice::from_raw_parts(rsp.signature.ptr, rsp.signature.len as usize);
                Ok(signature.to_vec())
            } else {
                Err(AcornError::Message(rust_string(err)).into())
            };
            (self.lib.free.sign.as_ref().expect("free.sign"))(std::ptr::null_mut(), &mut rsp);
            result
        }
    }

    fn verify(
        &self,
        alias: Option<&str>,
        key_hash: Option<&str>,
        domain: SpxDomain,
        message: &[u8],
        signature: &[u8],
    ) -> Result<bool> {
        let alias = alias.map(CString::new).transpose()?;
        let key_hash = key_hash.map(CString::new).transpose()?;
        let message = domain.prepare(message);
        // SAFETY: The signature returned by `sign` is copied into a rust Vec.
        // The memory allocated by the acorn library is freed by the acorn library's
        // free function.
        unsafe {
            let message = acorn_bindgen::acorn_buffer {
                ptr: message.as_ptr().cast_mut(),
                len: message.len() as u32,
            };
            let signature = acorn_bindgen::acorn_buffer {
                ptr: signature.as_ptr().cast_mut(),
                len: signature.len() as u32,
            };
            let mut rsp = acorn_bindgen::acorn_response_verify::default();
            let mut err = std::ptr::null_mut::<std::ffi::c_char>();
            let result = if (self.lib.func.verify.as_ref().expect("func.verify"))(
                alias
                    .as_ref()
                    .map(|x| x.as_ptr())
                    .unwrap_or(std::ptr::null()),
                key_hash
                    .as_ref()
                    .map(|x| x.as_ptr())
                    .unwrap_or(std::ptr::null()),
                message,
                signature,
                &mut rsp,
                &mut err,
            ) == 0
            {
                Ok(rsp.verified != 0)
            } else {
                Err(AcornError::Message(rust_string(err)).into())
            };
            (self.lib.free.verify.as_ref().expect("free.verify"))(std::ptr::null_mut(), &mut rsp);
            result
        }
    }
}
