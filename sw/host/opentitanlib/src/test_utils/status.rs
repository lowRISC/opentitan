// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
use serde::{Deserialize, Serialize};
use std::convert::TryFrom;
use thiserror::Error;

#[derive(Clone, Debug, Error, Serialize, Deserialize, PartialEq, Eq)]
pub enum Status {
    #[error("Not an error ({0})!")]
    Ok(u32),
    #[error("Cancelled (module={0} line={1})")]
    Cancelled(String, u32),
    #[error("Unknown (module={0} line={1})")]
    Unknown(String, u32),
    #[error("Invalid Argument (module={0} line={1})")]
    InvalidArgument(String, u32),
    #[error("Deadline Exceeded (module={0} line={1})")]
    DeadlineExceeded(String, u32),
    #[error("Not Found (module={0} line={1})")]
    NotFound(String, u32),
    #[error("Already Exists (module={0} line={1})")]
    AlreadyExists(String, u32),
    #[error("Permission Denied (module={0} line={1})")]
    PermissionDenied(String, u32),
    #[error("Resource Exhausted (module={0} line={1})")]
    ResourceExhausted(String, u32),
    #[error("Failed Precondition (module={0} line={1})")]
    FailedPrecondition(String, u32),
    #[error("Aborted (module={0} line={1})")]
    Aborted(String, u32),
    #[error("Out Of Range (module={0} line={1})")]
    OutOfRange(String, u32),
    #[error("Unimplemented (module={0} line={1})")]
    Unimplemented(String, u32),
    #[error("Internal (module={0} line={1})")]
    Internal(String, u32),
    #[error("Unavailable (module={0} line={1})")]
    Unavailable(String, u32),
    #[error("Data Loss (module={0} line={1})")]
    DataLoss(String, u32),
    #[error("Unauthenticated (module={0} line={1})")]
    Unauthenticated(String, u32),
}

#[allow(non_camel_case_types)]
pub type status_t = Status;

macro_rules! ok_status_to_integer {
    () => { };

    ($t:ty, $($ts:ty),* $(,)?) => {
        impl TryFrom<Status> for $t {
            type Error = Status;
            fn try_from(value: Status) -> Result<Self, Self::Error> {
                match value {
                    Status::Ok(v) => Ok(v as $t),
                    _ => Err(value),
                }
            }
        }
        ok_status_to_integer!($($ts,)*);
    };
}

// Facilitate easy conversion of Status::Ok(_) to integer types.
ok_status_to_integer!(u8, u16, u32, u64, usize, i8, i16, i32, i64, isize);

#[cfg(test)]
mod test {
    use super::*;
    use anyhow::Result;

    #[test]
    fn test_convert_ok() -> Result<()> {
        let status = Status::Ok(123);
        assert_eq!(123, i32::try_from(status)?);
        Ok(())
    }

    #[test]
    fn test_convert_err() -> Result<()> {
        let status = Status::Cancelled("foo".into(), 123);
        assert!(u32::try_from(status).is_err());
        Ok(())
    }
}
