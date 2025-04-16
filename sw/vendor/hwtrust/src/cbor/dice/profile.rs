//! Defines the set of validation rules to apply for a DICE profile.

use super::KeyOpsType;
use crate::dice::ProfileVersion;

/// Options that describe an Android Profile for DICE.
#[derive(Default)]
pub(super) struct Profile {
    /// The types that are permitted for the key_ops field of COSE_Key objects in the DICE chain.
    /// This option can be used for compatibility with the RKP HAL before v3 which diverged from
    /// the COSE spec and allowed a single int instead of always requiring an array.
    pub(super) key_ops_type: KeyOpsType,

    /// The types that are permitted for the mode field of the DICE certificates. This option can
    /// be used for compatibility with the RKP HAL v3 which allowed some deviations from the Open
    /// Profile for DICE specification.
    pub(super) mode_type: ModeType,

    /// Whether to allow the key_usage field of the DICE certificates to be encoded in big-endian
    /// byte order. This introduces ambiguity of the exact key usage being expressed but the keys
    /// in the DICE chain are only used for verification so it may be preferable to allow for
    /// compatibility with implementations that use the wrong endianness.
    pub(super) allow_big_endian_key_usage: bool,

    /// The types that are permitted for the component version field in the configuration
    /// descriptor. The specification has changed the allowed types over time and this option
    /// can be used to select which rules to apply.
    pub(super) component_version_type: ComponentVersionType,

    /// Whether the configuration hash is verified to be present and derived from the configuration
    /// descriptor. This allows for compatibility with early versions of the RKP HAL which did not
    /// enforce the requirements on the configuration hash as defined by the Open Profile for DICE.
    pub(super) config_hash_unverified: bool,

    /// Whether the security version is a required field in the configuration descriptor.
    pub(super) security_version_optional: bool,

    /// Whether the root certificate is allowed to have its mode set to debug.
    pub(super) allow_root_mode_debug: bool,

    /// Whether the root certificate's authority hash size is allowed to differ from its code hash size.
    pub(super) allow_root_varied_auth_hash_size: bool,
}

/// Type allowed for the DICE certificate mode field.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub(super) enum ModeType {
    /// The mode field must be a byte string holding a single byte as specified by the Open Profile
    /// for DICE.
    #[default]
    Bytes,
    /// The mode field can be either an int or a byte string holding a single byte.
    IntOrBytes,
}

/// Type allowed for the DICE certificate configuration descriptor's component version field.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub(super) enum ComponentVersionType {
    /// The component version can be either an int or a free-form string.
    #[default]
    IntOrString,
    /// The component version must be an int.
    Int,
}

impl Profile {
    /// The rules for the profile used in Android 13.
    pub(super) fn android13() -> Self {
        Self {
            // Context: b/262599829#comment65
            key_ops_type: KeyOpsType::IntOrArray,
            // Context: b/273552826
            component_version_type: ComponentVersionType::Int,
            config_hash_unverified: true,
            security_version_optional: true,
            ..Self::default()
        }
    }

    /// The rules for the "android.14" profile.
    pub(super) fn android14() -> Self {
        Self {
            // Context: b/273552826
            mode_type: ModeType::IntOrBytes,
            allow_big_endian_key_usage: true,
            config_hash_unverified: true,
            security_version_optional: true,
            allow_root_mode_debug: true,
            allow_root_varied_auth_hash_size: true,
            ..Self::default()
        }
    }

    /// The rules for the "android.15" profile.
    pub(super) fn android15() -> Self {
        Self { config_hash_unverified: true, security_version_optional: true, ..Self::default() }
    }

    /// The rules for the "android.16" profile..
    pub(super) fn android16() -> Self {
        Self::default()
    }
}

impl From<ProfileVersion> for Profile {
    fn from(version: ProfileVersion) -> Self {
        match version {
            ProfileVersion::Android13 => Profile::android13(),
            ProfileVersion::Android14 => Profile::android14(),
            ProfileVersion::Android15 => Profile::android15(),
            ProfileVersion::Android16 => Profile::android16(),
        }
    }
}
