use std::error::Error;
use std::fmt::{self, Display, Formatter};
use std::str::FromStr;

/// Versions of the Android Profile for DICE.
#[derive(Debug, Default, Copy, Clone, PartialEq, Eq, Ord, PartialOrd)]
pub enum ProfileVersion {
    /// The version of the Android Profile for DICE that aligns with Android 13.
    Android13,
    /// The version of the Android Profile for DICE that aligns with Android 14.
    #[default]
    Android14,
    /// The version of the Android Profile for DICE that aligns with Android 15.
    Android15,
    /// The version of the Android Profile for DICE that aligns with Android 16.
    Android16,
}

impl Display for ProfileVersion {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        let profile_name = match self {
            Self::Android13 => "android.13",
            Self::Android14 => "android.14",
            Self::Android15 => "android.15",
            Self::Android16 => "android.16",
        };
        write!(f, "{profile_name}",)
    }
}

/// An error which can be returned when parsing an Android Profile for DICE version.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct ParseProfileVersionError(());

impl fmt::Display for ParseProfileVersionError {
    fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
        write!(fmt, "unknown profile version")
    }
}

impl Error for ParseProfileVersionError {}

impl FromStr for ProfileVersion {
    type Err = ParseProfileVersionError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        Ok(match s {
            "android.14" => Self::Android14,
            "android.15" => Self::Android15,
            "android.16" => Self::Android16,
            _ => return Err(ParseProfileVersionError(())),
        })
    }
}
