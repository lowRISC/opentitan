//! Defines the context type for a session handling hwtrust data structures.

use crate::dice::ProfileVersion;
use anyhow::bail;
use clap::ValueEnum;
use std::ops::RangeInclusive;
use std::str::FromStr;

/// The context for a session handling hwtrust data structures.
#[derive(Clone, Default, Debug)]
pub struct Session {
    /// Options that control the behaviour during this session.
    pub options: Options,
}

/// Options that control the behaviour of a session.
#[derive(Clone, Default, Debug)]
pub struct Options {
    /// The range of supported Android Profile for DICE versions.
    pub dice_profile_range: DiceProfileRange,
    /// Allows DICE chains to have non-normal mode values.
    pub allow_any_mode: bool,
    /// The RKP instance associated to the session.
    pub rkp_instance: RkpInstance,
    /// This flag is used during DeviceInfo validation
    pub is_factory: bool,
    /// Verbose output
    pub verbose: bool,
}

/// The set of RKP instances associated to the session.
#[derive(Clone, Copy, Default, Debug, ValueEnum, PartialEq, Eq)]
pub enum RkpInstance {
    /// The DICE chain is associated to the default instance.
    #[default]
    Default,
    /// The DICE chain is associated to the strongbox instance.
    Strongbox,
    /// The DICE chain is associated to the avf instance.
    /// This option performs additional checks to ensure the chain conforms to the requirements
    /// for an RKP VM chain. For detailed information, refer to the RKP VM specification:
    /// https://android.googlesource.com/platform/packages/modules/Virtualization/+/main/docs/vm_remote_attestation.md#rkp-vm-marker
    Avf,
    /// The DICE chain is associated to the Widevine instance.
    Widevine,
}

impl FromStr for RkpInstance {
    type Err = anyhow::Error;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        match s {
            "default" => Ok(RkpInstance::Default),
            "strongbox" => Ok(RkpInstance::Strongbox),
            "avf" => Ok(RkpInstance::Avf),
            "widevine" => Ok(RkpInstance::Widevine),
            _ => bail!("invalid RKP instance: {}", s),
        }
    }
}

impl Session {
    /// Set is_factory
    pub fn set_is_factory(&mut self, is_factory: bool) {
        self.options.is_factory = is_factory;
    }

    /// Set allow_any_mode.
    pub fn set_allow_any_mode(&mut self, allow_any_mode: bool) {
        self.options.allow_any_mode = allow_any_mode
    }

    /// Sets the RKP instance associated to the session.
    pub fn set_rkp_instance(&mut self, rkp_instance: RkpInstance) {
        self.options.rkp_instance = rkp_instance
    }
}

/// An inclusive range of Android Profile for DICE versions.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DiceProfileRange(RangeInclusive<ProfileVersion>);

impl DiceProfileRange {
    /// Creates a new inclusive range of Android Profile for DICE versions.
    pub fn new(start: ProfileVersion, end: ProfileVersion) -> Self {
        Self(RangeInclusive::new(start, end))
    }

    /// Returns `true` if `version` is contained in the range.
    pub fn contains(&self, version: ProfileVersion) -> bool {
        self.0.contains(&version)
    }

    /// Returns the lower bound of the range.
    pub fn start(&self) -> ProfileVersion {
        *self.0.start()
    }

    /// Returns the upper bound of the range.
    pub fn end(&self) -> ProfileVersion {
        *self.0.end()
    }
}

impl Default for DiceProfileRange {
    fn default() -> Self {
        Self::new(ProfileVersion::Android14, ProfileVersion::Android16)
    }
}

impl Options {
    /// The options use by VSR 13.
    pub fn vsr13() -> Self {
        Self {
            dice_profile_range: DiceProfileRange::new(
                ProfileVersion::Android13,
                ProfileVersion::Android15,
            ),
            ..Default::default()
        }
    }

    /// The options use by VSR 14.
    pub fn vsr14() -> Self {
        Self {
            dice_profile_range: DiceProfileRange::new(
                ProfileVersion::Android14,
                ProfileVersion::Android15,
            ),
            ..Default::default()
        }
    }

    /// The options use by VSR 15.
    pub fn vsr15() -> Self {
        Self {
            dice_profile_range: DiceProfileRange::new(
                ProfileVersion::Android14,
                ProfileVersion::Android15,
            ),
            ..Default::default()
        }
    }

    /// The options use by VSR 16.
    pub fn vsr16() -> Self {
        Self {
            dice_profile_range: DiceProfileRange::new(
                ProfileVersion::Android14,
                ProfileVersion::Android16,
            ),
            ..Default::default()
        }
    }
}
