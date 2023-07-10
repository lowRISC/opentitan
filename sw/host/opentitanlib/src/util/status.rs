// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// This utility handles the various aspect of the status_t type used in
// the device code.

use anyhow::{bail, Context, Result};
use bindgen::status::{ot_status_create_record_t, status_create, status_err, status_extract};

use object::{Object, ObjectSection};

use num_enum::TryFromPrimitive;

use std::convert::TryFrom;
use std::ffi::CString;
use std::path::PathBuf;

pub use bindgen::status::absl_status_t as RawStatusCode;
pub use bindgen::status::status_t as RawStatus;

// FIXME: is there a better way of doing this? bindgen CLI does not
// support adding custom derive to a type.
#[derive(Debug, serde::Serialize, serde::Deserialize, TryFromPrimitive, PartialEq, Eq)]
#[repr(u32)]
pub enum StatusCode {
    Ok = bindgen::status::absl_status_code_kOk,
    Cancelled = bindgen::status::absl_status_code_kCancelled,
    Unknown = bindgen::status::absl_status_code_kUnknown,
    InvalidArgument = bindgen::status::absl_status_code_kInvalidArgument,
    DeadlineExceeded = bindgen::status::absl_status_code_kDeadlineExceeded,
    NotFound = bindgen::status::absl_status_code_kNotFound,
    AlreadyExists = bindgen::status::absl_status_code_kAlreadyExists,
    PermissionDenied = bindgen::status::absl_status_code_kPermissionDenied,
    ResourceExhausted = bindgen::status::absl_status_code_kResourceExhausted,
    FailedPrecondition = bindgen::status::absl_status_code_kFailedPrecondition,
    Aborted = bindgen::status::absl_status_code_kAborted,
    OutOfRange = bindgen::status::absl_status_code_kOutOfRange,
    Unimplemented = bindgen::status::absl_status_code_kUnimplemented,
    Internal = bindgen::status::absl_status_code_kInternal,
    Unavailable = bindgen::status::absl_status_code_kUnavailable,
    DataLoss = bindgen::status::absl_status_code_kDataLoss,
    Unauthenticated = bindgen::status::absl_status_code_kUnauthenticated,
}

// Safe abstraction over status_create
fn status_create_safe(code: StatusCode, mod_id: u32, file: String, arg: i32) -> RawStatus {
    // We do not expect an error since it is a valid String.
    let file = CString::new(file).expect("CString::new failed");
    unsafe {
        // Safety: the function expects a valid readonly C-string which is exactly what
        // CString:as_ptr() provides.
        status_create(code as u32, mod_id, file.as_ptr(), arg)
    }
    // Note: file is dropped here so the C-string pointer is valid accross the function call.
}

// Convert an array of i8 to a string. This function will stop at first 0 (or at the
// end of the array if it contains no zero).
fn c_string_to_string(array: &[i8]) -> String {
    let array = array
        .iter()
        .map(|c| *c as u8)
        .take_while(|c| *c != 0u8)
        .collect::<Vec<_>>();
    String::from_utf8_lossy(&array).to_string()
}

#[derive(Debug, serde::Serialize, serde::Deserialize)]
/// Hold a completely decoded status.
pub struct Status {
    // Module ID if present.
    pub module_id: String,
    // Status argument. Note that depending on whether this is an error status or ok
    // status, the maximum value that can fit is different.
    pub arg: i32,
    // Error code of the status.
    pub code: StatusCode,
}

// Safe abstraction over status_extract.
impl Status {
    pub fn from_raw_status(status: RawStatus) -> Result<Status> {
        // We do not care about the code string but status_extract expects a non-null pointer.
        let mut _code_str: *const std::os::raw::c_char = std::ptr::null();
        let mut arg = 0i32;
        let mut mod_id: [std::os::raw::c_char; 3] = [0; 3];
        let is_err_status = unsafe {
            // Safety: status_extract expects:
            // - a non-null pointer to string pointer that will be updated to point
            //   to the english name of the error code,
            // - a non-null pointer to an integer (argument),
            // - a non-null pointer to a char[3] buffer that is filled with the module ID.
            status_extract(status, &mut _code_str, &mut arg, &mut mod_id as *mut i8)
        };
        let code = match is_err_status {
            false => StatusCode::Ok,
            true => {
                // Safety: nothing unsafe except that it's an FFI call.
                let raw_code = unsafe { status_err(status) };
                StatusCode::try_from(raw_code)?
            }
        };
        Ok(Status {
            module_id: c_string_to_string(&mod_id),
            arg,
            code,
        })
    }

    pub fn from_u32(status: u32) -> Result<Status> {
        Self::from_raw_status(RawStatus {
            value: status as i32,
        })
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn status_manip_test_good() {
        // Make sure that we can correctly decode a status. For this, we first need to
        // create it.
        const CODE: StatusCode = StatusCode::PermissionDenied;
        const MOD_ID: &str = "abc";
        const ARG: i32 = 42;
        let mod_id_bytes = MOD_ID.as_bytes();
        assert_eq!(mod_id_bytes.len(), 3);
        // Unfortunately the input to status_create assumes that the module ID value
        // is already shifted and we cannot extract the MAKE_MODULE_ID macro from the
        // headers using bindgen.
        let mod_id_val = ((mod_id_bytes[0].to_ascii_uppercase() as u32) << 16)
            | ((mod_id_bytes[1].to_ascii_uppercase() as u32) << 21)
            | ((mod_id_bytes[2].to_ascii_uppercase() as u32) << 26);
        let raw_status = status_create_safe(CODE, mod_id_val, "".to_string(), ARG);

        // Now decode status.
        let decoded_status = Status::from_raw_status(raw_status);
        assert!(decoded_status.is_ok());
        let decoded_status = decoded_status.unwrap();
        assert_eq!(decoded_status.module_id, MOD_ID.to_ascii_uppercase());
        assert_eq!(decoded_status.code, CODE);
        assert_eq!(decoded_status.arg, ARG);
    }
}

#[derive(Debug, serde::Serialize, serde::Deserialize)]
/// Hold a status creation record as stored in the special ELF section of an executable.
pub struct StatusCreateRecord {
    // Module ID, or None if it is not specified (in which case it computed at runtime
    // by status_create based on the filename).
    pub module_id: Option<u32>,
    // Name of the file that creates this status.
    pub filename: String,
}

impl StatusCreateRecord {
    /// Compute the Module ID actually created by status_create on device, that is either the
    /// module_id or comes from the filename.
    pub fn get_module_id(&self) -> Result<String> {
        // In order to avoid reimplementing the algorithm, we first create a temporary
        // status with status_create that we then decode using status_extract.
        // If the value of MODULE_ID was not overriden in the file, then it is defined as
        //   extern const uint32_t MODULE_ID;
        // in status.h, and therefore it is not known at compile time. In this case, on the
        // actual device, the value of MODULE_ID is 0.
        const DEFAULT_MODULE_ID: u32 = 0;

        let mod_id = self.module_id.map_or(DEFAULT_MODULE_ID, |mod_id| mod_id);
        // We need to use a non-ok error code, otherwise the module ID is not stored.
        let status = status_create_safe(StatusCode::Unknown, mod_id, self.filename.clone(), 0);
        let status = Status::from_raw_status(status)?;
        Ok(status.module_id)
    }
}

// Fields that are unknown at compile time use special value.
const UNKNOWN_MODULE_ID: u32 = bindgen::status::ot_status_create_record_magic_OT_SCR_UNKNOWN_MOD_ID;

impl TryFrom<ot_status_create_record_t> for StatusCreateRecord {
    type Error = anyhow::Error;

    fn try_from(record: ot_status_create_record_t) -> Result<StatusCreateRecord> {
        // A C string is an array of char so bindgen creates an array of i8, so we need to
        // convert it to an array of u8. Furthermore, since it is a fixed-size array, it contains
        // a lot of zeroes at the end which CString does not like and that we need to remove.
        let filename = c_string_to_string(&record.filename);

        Ok(StatusCreateRecord {
            module_id: Some(record.module_id).filter(|mod_id| mod_id != &UNKNOWN_MODULE_ID),
            filename,
        })
    }
}

#[derive(Debug, serde::Serialize, serde::Deserialize)]
/// Hold a collection of status creation records
pub struct StatusCreateRecords {
    pub records: Vec<StatusCreateRecord>,
}

impl StatusCreateRecords {
    /// Return the name of the file(s) that match a given module ID.
    pub fn find_module_id(&self, mod_id: &String) -> Vec<String> {
        let iter = self
            .records
            .iter()
            .filter(|rec| rec.get_module_id().map_or(false, |id| id == *mod_id))
            .map(|rec| rec.filename.clone());
        std::collections::HashSet::<String>::from_iter(iter)
            .into_iter()
            .collect()
    }
}

pub fn load_elf(elf_file: &PathBuf) -> Result<StatusCreateRecords> {
    let file_data = std::fs::read(elf_file)
        .with_context(|| format!("Could not read ELF file {}.", elf_file.display()))?;
    let file = object::File::parse(&*file_data)
        .with_context(|| format!("Could not parse ELF file {}", elf_file.display()))?;
    // Try to find the .ot.status_create_record section.
    let section = file
        .section_by_name(".ot.status_create_record")
        .ok_or_else(|| {
            anyhow::anyhow!("ELF file should have a .ot.status_create_record section")
        })?;
    let status_create_records = section
        .data()
        .context("cannot read .ot.status_create_record section data")?;
    // Make sure that the section size is a multiple of the record size.
    const RECORD_SIZE: usize = std::mem::size_of::<ot_status_create_record_t>();
    if status_create_records.len() % RECORD_SIZE != 0 {
        bail!(".ot.status_create_record section size ({}) is not a multiple of the ot_status_create_record_t size ({})",
              status_create_records.len(), RECORD_SIZE);
    }
    // Conversion is unsafe but since the structure is packed and contains only POD,
    // it really is safe.
    let records = status_create_records
        .chunks(RECORD_SIZE)
        .map(|chunk| unsafe {
            // We need to provide transmute with a fixed-size array but chunk does not give us one.
            // If/When as_chunks is stabilized, we can get rid of this conversion.
            let chunk = <[u8; RECORD_SIZE]>::try_from(chunk).unwrap();
            std::mem::transmute::<[u8; RECORD_SIZE], ot_status_create_record_t>(chunk)
        })
        .map(StatusCreateRecord::try_from)
        .collect::<Result<_>>()?;
    Ok(StatusCreateRecords { records })
}
