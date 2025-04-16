use super::cose_key_from_cbor_value;
use super::profile::{ComponentVersionType, ModeType, Profile};
use crate::cbor::{field_value::FieldValue, serialize, value_from_bytes};
use crate::dice::{
    ComponentVersion, ConfigDesc, ConfigDescBuilder, DiceMode, Payload, PayloadBuilder,
    ProfileVersion,
};
use crate::publickey::PublicKey;
use crate::session::Session;
use anyhow::{anyhow, bail, ensure, Context, Result};
use ciborium::value::Value;
use coset::{AsCborValue, CoseSign1};
use openssl::sha::{sha256, sha384, sha512};
use std::collections::hash_map::Entry::{Occupied, Vacant};
use std::collections::HashMap;
use std::str::FromStr;

const ISS: i64 = 1;
const SUB: i64 = 2;
const CODE_HASH: i64 = -4670545;
const CODE_DESC: i64 = -4670546;
const CONFIG_HASH: i64 = -4670547;
const CONFIG_DESC: i64 = -4670548;
const AUTHORITY_HASH: i64 = -4670549;
const AUTHORITY_DESC: i64 = -4670550;
const MODE: i64 = -4670551;
const SUBJECT_PUBLIC_KEY: i64 = -4670552;
const KEY_USAGE: i64 = -4670553;
const PROFILE_NAME: i64 = -4670554;

const CONFIG_DESC_RESERVED_MAX: i64 = -70000;
const CONFIG_DESC_RESERVED_MIN: i64 = -70999;
const COMPONENT_NAME: i64 = -70002;
const COMPONENT_VERSION: i64 = -70003;
const RESETTABLE: i64 = -70004;
const SECURITY_VERSION: i64 = -70005;
const RKP_VM_MARKER: i64 = -70006;
const COMPONENT_INSTANCE_NAME: i64 = -70007;

pub(super) struct Entry {
    payload: Vec<u8>,
}

impl Entry {
    pub(super) fn verify_cbor_value(cbor: Value, key: &PublicKey) -> Result<Self> {
        let sign1 = CoseSign1::from_cbor_value(cbor)
            .context("Given CBOR does not appear to be a COSE_sign1")?;
        key.verify_cose_sign1(&sign1, b"").context("cannot verify COSE_sign1")?;
        match sign1.payload {
            None => bail!("Missing payload"),
            Some(payload) => Ok(Self { payload }),
        }
    }

    pub(super) fn payload(&self) -> &[u8] {
        &self.payload
    }
}

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub(super) enum ConfigFormat {
    /// The configuration descriptor format specified by Android.
    #[default]
    Android,
    /// The configuration descriptor format is either that specified by Android or is ignored.
    AndroidOrIgnored,
}

impl Payload {
    pub(super) fn from_cbor(
        session: &Session,
        bytes: &[u8],
        config_format: ConfigFormat,
        is_root: bool,
    ) -> Result<Self> {
        let entries = cbor_map_from_slice(bytes)?;
        let profile_version = PayloadFields::extract_profile_version(session, &entries)?;
        Self::from_entries(
            &profile_version.into(),
            entries,
            config_format,
            is_root,
            session.options.allow_any_mode,
        )
    }

    fn from_entries(
        profile: &Profile,
        entries: Vec<(Value, Value)>,
        config_format: ConfigFormat,
        is_root: bool,
        allow_any_mode: bool,
    ) -> Result<Self> {
        let f =
            PayloadFields::from_entries(profile, entries, config_format, is_root, allow_any_mode)?;
        PayloadBuilder::with_subject_public_key(f.subject_public_key)
            .issuer(f.issuer)
            .subject(f.subject)
            .mode(f.mode.ok_or_else(|| anyhow!("mode required"))?)
            .code_desc(f.code_desc)
            .code_hash(f.code_hash.ok_or_else(|| anyhow!("code hash required"))?)
            .config_desc(f.config_desc.ok_or_else(|| anyhow!("config desc required"))?)
            .config_hash(f.config_hash)
            .authority_desc(f.authority_desc)
            .authority_hash(f.authority_hash.ok_or_else(|| anyhow!("authority hash required"))?)
            .build()
            .context("building payload")
    }
}

pub(super) struct PayloadFields {
    pub(super) issuer: String,
    pub(super) subject: String,
    pub(super) subject_public_key: PublicKey,
    mode: Option<DiceMode>,
    code_desc: Option<Vec<u8>>,
    code_hash: Option<Vec<u8>>,
    config_desc: Option<ConfigDesc>,
    config_hash: Option<Vec<u8>>,
    authority_desc: Option<Vec<u8>>,
    authority_hash: Option<Vec<u8>>,
}

impl PayloadFields {
    pub(super) fn from_cbor(
        session: &Session,
        bytes: &[u8],
        config_format: ConfigFormat,
        is_root: bool,
        possibly_degenerate: bool,
    ) -> Result<Self> {
        let entries = cbor_map_from_slice(bytes)?;
        let profile_version = Self::extract_profile_version(session, &entries)?;
        let allow_any_mode = session.options.allow_any_mode || possibly_degenerate;

        Self::from_entries(&profile_version.into(), entries, config_format, is_root, allow_any_mode)
    }

    fn extract_profile_version(
        session: &Session,
        entries: &[(Value, Value)],
    ) -> Result<ProfileVersion> {
        let mut profile_name = FieldValue::new("profile name");
        for (key, value) in entries.iter() {
            if key == &Value::from(PROFILE_NAME) {
                profile_name.set_once(value.clone())?;
            }
        }

        let profile_version = match profile_name.into_optional_string()? {
            None => {
                let version = session.options.dice_profile_range.start();
                ensure!(version <= ProfileVersion::Android14, "profile name is required");
                version
            }
            Some(profile_name) => {
                ProfileVersion::from_str(&profile_name).with_context(|| profile_name.clone())?
            }
        };
        ensure!(
            session.options.dice_profile_range.contains(profile_version),
            "profile version \"{profile_version}\" is less than \"{}\" or greater than \"{}\"",
            session.options.dice_profile_range.start(),
            session.options.dice_profile_range.end(),
        );

        Ok(profile_version)
    }

    fn from_entries(
        profile: &Profile,
        entries: Vec<(Value, Value)>,
        config_format: ConfigFormat,
        is_root: bool,
        allow_any_mode: bool,
    ) -> Result<Self> {
        let mut issuer = FieldValue::new("issuer");
        let mut subject = FieldValue::new("subject");
        let mut subject_public_key = FieldValue::new("subject public key");
        let mut mode = FieldValue::new("mode");
        let mut code_desc = FieldValue::new("code desc");
        let mut code_hash = FieldValue::new("code hash");
        let mut config_desc = FieldValue::new("config desc");
        let mut config_hash = FieldValue::new("config hash");
        let mut authority_desc = FieldValue::new("authority desc");
        let mut authority_hash = FieldValue::new("authority hash");
        let mut key_usage = FieldValue::new("key usage");
        let mut profile_name = FieldValue::new("profile name");

        for (key, value) in entries.into_iter() {
            if let Some(Ok(key)) = key.as_integer().map(TryInto::try_into) {
                let field = match key {
                    ISS => &mut issuer,
                    SUB => &mut subject,
                    SUBJECT_PUBLIC_KEY => &mut subject_public_key,
                    MODE => &mut mode,
                    CODE_DESC => &mut code_desc,
                    CODE_HASH => &mut code_hash,
                    CONFIG_DESC => &mut config_desc,
                    CONFIG_HASH => &mut config_hash,
                    AUTHORITY_DESC => &mut authority_desc,
                    AUTHORITY_HASH => &mut authority_hash,
                    KEY_USAGE => &mut key_usage,
                    PROFILE_NAME => &mut profile_name,
                    _ => bail!("Unknown key {}", key),
                };
                field.set_once(value)?
            } else {
                bail!("Invalid key: {:?}", key);
            }
        }

        validate_key_usage(profile, key_usage)?;
        let (config_desc, config_hash) =
            validate_config(profile, config_desc, config_hash, config_format).context("config")?;

        let (code_hash, authority_hash) =
            validate_hash_sizes(profile, code_hash, &config_hash, authority_hash, is_root)?;

        Ok(Self {
            issuer: issuer.into_string()?,
            subject: subject.into_string()?,
            subject_public_key: validate_subject_public_key(profile, subject_public_key)?,
            mode: validate_mode(profile, mode, is_root, allow_any_mode)?,
            code_desc: code_desc.into_optional_bytes()?,
            code_hash,
            config_desc,
            config_hash,
            authority_desc: authority_desc.into_optional_bytes()?,
            authority_hash,
        })
    }
}

fn validate_hash_sizes(
    profile: &Profile,
    code_hash: FieldValue,
    config_hash: &Option<Vec<u8>>,
    authority_hash: FieldValue,
    is_root: bool,
) -> Result<(Option<Vec<u8>>, Option<Vec<u8>>)> {
    let code_hash = code_hash.into_optional_bytes()?;
    let authority_hash: Option<Vec<u8>> = authority_hash.into_optional_bytes()?;

    if let Some(ref code_hash) = code_hash {
        let used_hash_size = code_hash.len();

        if ![32, 48, 64].contains(&(used_hash_size)) {
            bail!("bad code hash size, actual: {0}, expected: 32, 48, or 64", used_hash_size)
        }

        if let Some(ref config_hash) = config_hash {
            if config_hash.len() != used_hash_size {
                bail!(
                    "bad config hash size, actual: {0}, expected: {1}",
                    config_hash.len(),
                    used_hash_size
                )
            }
        }

        if let Some(ref authority_hash) = authority_hash {
            let root_exception = profile.allow_root_varied_auth_hash_size && is_root;
            if authority_hash.len() != used_hash_size && !root_exception {
                bail!(
                    "bad authority hash size, actual: {0}, expected: {1}",
                    authority_hash.len(),
                    used_hash_size
                )
            }
        }
    }

    Ok((code_hash, authority_hash))
}

fn validate_key_usage(profile: &Profile, key_usage: FieldValue) -> Result<()> {
    let key_usage = key_usage.into_bytes().context("key usage")?;
    let key_cert_sign = 1 << 5;
    if key_usage.len() > 1
        && profile.allow_big_endian_key_usage
        && key_usage[key_usage.len() - 1] == key_cert_sign
        && key_usage.iter().take(key_usage.len() - 1).all(|&x| x == 0)
    {
        return Ok(());
    }
    if key_usage.is_empty()
        || key_usage[0] != key_cert_sign
        || !key_usage.iter().skip(1).all(|&x| x == 0)
    {
        bail!("key usage must only contain keyCertSign (bit 5)");
    };
    Ok(())
}

fn validate_subject_public_key(
    profile: &Profile,
    subject_public_key: FieldValue,
) -> Result<PublicKey> {
    let subject_public_key = subject_public_key.into_bytes()?;
    let subject_public_key = value_from_bytes(&subject_public_key).context("decode CBOR")?;
    let subject_public_key = cose_key_from_cbor_value(subject_public_key, profile.key_ops_type)
        .context("parsing subject public key")?;
    PublicKey::from_cose_key(&subject_public_key)
        .context("parsing subject public key from COSE_key")
}

fn validate_mode(
    profile: &Profile,
    mode: FieldValue,
    is_root: bool,
    allow_any_mode: bool,
) -> Result<Option<DiceMode>> {
    if !mode.is_bytes() && profile.mode_type == ModeType::IntOrBytes {
        mode.into_optional_i64()?
    } else {
        mode.into_optional_bytes()?
            .map(|mode| {
                if mode.len() != 1 {
                    bail!("Expected mode to be a single byte, actual byte count: {}", mode.len())
                };
                Ok(mode[0].into())
            })
            .transpose()?
    }
    .map(|mode| {
        let mode = match mode {
            1 => DiceMode::Normal,
            2 => DiceMode::Debug,
            3 => DiceMode::Recovery,
            _ => DiceMode::NotConfigured,
        };

        if mode != DiceMode::Normal && !allow_any_mode {
            let debug_allowed = is_root && profile.allow_root_mode_debug;
            ensure!(debug_allowed, "Expected mode to be normal, actual mode: {:?}", mode);
            ensure!(
                mode == DiceMode::Debug,
                "Expected mode to be normal or debug, actual mode: {:?}",
                mode
            );
        }
        Ok(mode)
    })
    .transpose()
}

fn validate_config(
    profile: &Profile,
    config_desc: FieldValue,
    config_hash: FieldValue,
    config_format: ConfigFormat,
) -> Result<(Option<ConfigDesc>, Option<Vec<u8>>)> {
    let config_desc = config_desc.into_optional_bytes()?;
    let config_hash = config_hash.into_optional_bytes()?;
    if let Some(config_desc) = config_desc {
        let config = config_desc_from_slice(profile, &config_desc).context("parsing descriptor");
        if config.is_err() && config_format == ConfigFormat::AndroidOrIgnored {
            return Ok((Some(ConfigDesc::default()), config_hash));
        }
        if !profile.config_hash_unverified {
            let Some(ref hash) = config_hash else { bail!("hash required") };
            match hash.len() {
                32 => ensure!(hash == &sha256(&config_desc)),
                48 => ensure!(hash == &sha384(&config_desc)),
                64 => ensure!(hash == &sha512(&config_desc)),
                _ => bail!("unsupported hash size"),
            };
        }
        Ok((Some(config?), config_hash))
    } else {
        Ok((None, config_hash))
    }
}

fn cbor_map_from_slice(bytes: &[u8]) -> Result<Vec<(Value, Value)>> {
    let value = value_from_bytes(bytes).context("Error parsing CBOR into a map")?;
    let entries = match value {
        Value::Map(entries) => entries,
        _ => bail!("Not a map: {:?}", value),
    };
    Ok(entries)
}

fn config_desc_from_slice(profile: &Profile, bytes: &[u8]) -> Result<ConfigDesc> {
    let entries = cbor_map_from_slice(bytes)?;

    let mut component_name = FieldValue::new("component name");
    let mut component_instance_name = FieldValue::new("component instance name");
    let mut component_version = FieldValue::new("component version");
    let mut resettable = FieldValue::new("resettable");
    let mut security_version = FieldValue::new("security version");
    let mut rkp_vm_marker = FieldValue::new("rkp vm marker");
    let mut extensions = HashMap::new();

    for (key, value) in entries.into_iter() {
        if let Some(Ok(key)) = key.as_integer().map(TryInto::try_into) {
            let field = match key {
                COMPONENT_NAME => &mut component_name,
                COMPONENT_INSTANCE_NAME => &mut component_instance_name,
                COMPONENT_VERSION => &mut component_version,
                RESETTABLE => &mut resettable,
                SECURITY_VERSION => &mut security_version,
                RKP_VM_MARKER => &mut rkp_vm_marker,
                key if (CONFIG_DESC_RESERVED_MIN..=CONFIG_DESC_RESERVED_MAX).contains(&key) => {
                    bail!("Reserved key {}", key);
                }
                _ => match extensions.entry(key) {
                    Vacant(entry) => {
                        entry.insert(value);
                        continue;
                    }
                    Occupied(entry) => {
                        bail!("Duplicate values for {}: {:?} and {:?}", key, entry.get(), value)
                    }
                },
            };
            field.set_once(value)?
        } else {
            bail!("Invalid key: {:?}", key);
        }
    }

    let extensions = extensions.into_iter().map(|(k, v)| (k, serialize(v))).collect();

    let security_version = if profile.security_version_optional {
        security_version.into_optional_u64()
    } else {
        security_version.into_u64().map(Some)
    }
    .context("Security version")?;

    Ok(ConfigDescBuilder::new()
        .component_name(component_name.into_optional_string().context("Component name")?)
        .component_instance_name(
            component_instance_name.into_optional_string().context("Component instance name")?,
        )
        .component_version(
            validate_version(profile, component_version).context("Component version")?,
        )
        .resettable(resettable.is_null().context("Resettable")?)
        .security_version(security_version)
        .rkp_vm_marker(rkp_vm_marker.is_null().context("RKP VM marker")?)
        .extensions(extensions)
        .build())
}

fn validate_version(profile: &Profile, field: FieldValue) -> Result<Option<ComponentVersion>> {
    Ok(
        if !field.is_integer()
            && profile.component_version_type == ComponentVersionType::IntOrString
        {
            field.into_optional_string()?.map(ComponentVersion::String)
        } else {
            field.into_optional_i64()?.map(ComponentVersion::Integer)
        },
    )
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::cbor::dice::KeyOpsType;
    use crate::cbor::serialize;
    use crate::publickey::testkeys::{PrivateKey, ED25519_KEY_PEM};
    use crate::session::{DiceProfileRange, Options};
    use ciborium::cbor;
    use coset::iana::{self, EnumI64};
    use coset::CborSerializable;
    use std::collections::HashMap;

    const ALLOW_ANY_MODE: bool = true;
    const IS_ROOT: bool = true;
    const POSSIBLY_DEGENERATE: bool = true;

    impl Entry {
        pub(in super::super) fn from_payload(payload: &Payload) -> Result<Self> {
            Ok(Self { payload: serialize(payload.to_cbor_value()?) })
        }

        pub(in super::super) fn sign(self, key: &PrivateKey) -> CoseSign1 {
            key.sign_cose_sign1(self.payload)
        }
    }

    impl Payload {
        pub(in super::super) fn to_cbor_value(&self) -> Result<Value> {
            let subject_public_key = self.subject_public_key().to_cose_key()?.to_vec()?;
            let config_desc = serialize(self.config_desc().to_cbor_value());
            let mut map = vec![
                (Value::from(ISS), Value::from(self.issuer())),
                (Value::from(SUB), Value::from(self.subject())),
                (Value::from(SUBJECT_PUBLIC_KEY), Value::from(subject_public_key)),
                (Value::from(MODE), encode_mode(self.mode())),
                (Value::from(CODE_HASH), Value::from(self.code_hash())),
                (Value::from(CONFIG_DESC), Value::from(config_desc)),
                (Value::from(AUTHORITY_HASH), Value::from(self.authority_hash())),
                (Value::from(KEY_USAGE), Value::from(vec![0x20])),
            ];
            if let Some(code_desc) = self.code_desc() {
                map.push((Value::from(CODE_DESC), Value::from(code_desc)));
            }
            if let Some(config_hash) = self.config_hash() {
                map.push((Value::from(CONFIG_HASH), Value::from(config_hash)));
            }
            if let Some(authority_desc) = self.authority_desc() {
                map.push((Value::from(AUTHORITY_DESC), Value::from(authority_desc)));
            }
            Ok(Value::Map(map))
        }
    }

    impl ConfigDesc {
        pub(in super::super) fn to_cbor_value(&self) -> Value {
            let mut map = Vec::new();
            if let Some(component_name) = self.component_name() {
                map.push((Value::from(COMPONENT_NAME), Value::from(component_name)));
            }
            if let Some(component_version) = self.component_version() {
                map.push((
                    Value::from(COMPONENT_VERSION),
                    match component_version {
                        ComponentVersion::Integer(n) => Value::from(*n),
                        ComponentVersion::String(s) => Value::from(s.as_str()),
                    },
                ))
            }
            if self.resettable() {
                map.push((Value::from(RESETTABLE), Value::Null));
            }
            if let Some(security_version) = self.security_version() {
                map.push((Value::from(SECURITY_VERSION), Value::from(security_version)));
            }
            if self.rkp_vm_marker() {
                map.push((Value::from(RKP_VM_MARKER), Value::Null));
            }
            Value::Map(map)
        }
    }

    fn encode_mode(mode: DiceMode) -> Value {
        let mode = match mode {
            DiceMode::NotConfigured => 0,
            DiceMode::Normal => 1,
            DiceMode::Debug => 2,
            DiceMode::Recovery => 3,
        };
        Value::Bytes(vec![mode])
    }

    #[test]
    fn valid_payload_sha256() {
        let config_desc = serialize(cbor!({COMPONENT_NAME => "sha256 test"}).unwrap());
        let config_hash = sha256(&config_desc).to_vec();
        let mut fields = valid_payload_fields();
        fields.insert(CODE_HASH, Value::Bytes(vec![1; 32]));
        fields.insert(CONFIG_DESC, Value::Bytes(config_desc));
        fields.insert(CONFIG_HASH, Value::Bytes(config_hash));
        fields.insert(AUTHORITY_HASH, Value::Bytes(vec![2; 32]));
        let session = Session { options: Options::default() };
        Payload::from_cbor(&session, &serialize_fields(fields), ConfigFormat::Android, !IS_ROOT)
            .unwrap();
    }

    #[test]
    fn valid_payload_sha384() {
        let config_desc = serialize(cbor!({COMPONENT_NAME => "sha384 test"}).unwrap());
        let config_hash = sha384(&config_desc).to_vec();
        let mut fields = valid_payload_fields();
        fields.insert(CODE_HASH, Value::Bytes(vec![1; 48]));
        fields.insert(CONFIG_DESC, Value::Bytes(config_desc));
        fields.insert(CONFIG_HASH, Value::Bytes(config_hash));
        fields.insert(AUTHORITY_HASH, Value::Bytes(vec![2; 48]));
        let session = Session { options: Options::default() };
        Payload::from_cbor(&session, &serialize_fields(fields), ConfigFormat::Android, !IS_ROOT)
            .unwrap();
    }

    #[test]
    fn valid_payload_sha512() {
        let fields = valid_payload_fields();
        let session = Session { options: Options::default() };
        Payload::from_cbor(&session, &serialize_fields(fields), ConfigFormat::Android, !IS_ROOT)
            .unwrap();
    }

    #[test]
    fn key_usage_only_key_cert_sign() {
        let mut fields = valid_payload_fields();
        fields.insert(KEY_USAGE, Value::Bytes(vec![0x20]));
        let session = Session { options: Options::default() };
        Payload::from_cbor(&session, &serialize_fields(fields), ConfigFormat::Android, !IS_ROOT)
            .unwrap();
    }

    #[test]
    fn key_usage_too_long() {
        let mut fields = valid_payload_fields();
        fields.insert(KEY_USAGE, Value::Bytes(vec![0x20, 0x30, 0x40]));
        let session = Session { options: Options::default() };
        Payload::from_cbor(&session, &serialize_fields(fields), ConfigFormat::Android, !IS_ROOT)
            .unwrap_err();
    }

    #[test]
    fn key_usage_lacks_key_cert_sign() {
        let mut fields = valid_payload_fields();
        fields.insert(KEY_USAGE, Value::Bytes(vec![0x10]));
        let session = Session { options: Options::default() };
        Payload::from_cbor(&session, &serialize_fields(fields), ConfigFormat::Android, !IS_ROOT)
            .unwrap_err();
    }

    #[test]
    fn key_usage_not_just_key_cert_sign() {
        let mut fields = valid_payload_fields();
        fields.insert(KEY_USAGE, Value::Bytes(vec![0x21]));
        let session = Session { options: Options::default() };
        Payload::from_cbor(&session, &serialize_fields(fields), ConfigFormat::Android, !IS_ROOT)
            .unwrap_err();
    }

    #[test]
    fn bad_code_hash_size() {
        let mut fields = valid_payload_fields();
        fields.insert(CODE_HASH, Value::Bytes(vec![1; 16]));
        let session = Session { options: Options::default() };
        Payload::from_cbor(&session, &serialize_fields(fields), ConfigFormat::Android, !IS_ROOT)
            .unwrap_err();
    }

    #[test]
    fn bad_authority_hash_size() {
        let mut fields = valid_payload_fields();
        fields.insert(AUTHORITY_HASH, Value::Bytes(vec![1; 16]));
        let session = Session { options: Options::default() };
        Payload::from_cbor(&session, &serialize_fields(fields), ConfigFormat::Android, !IS_ROOT)
            .unwrap_err();
    }

    #[test]
    fn inconsistent_authority_hash_size() {
        let mut fields = valid_payload_fields();
        fields.insert(AUTHORITY_HASH, Value::Bytes(vec![1; 32]));
        let session = Session { options: Options::default() };
        Payload::from_cbor(&session, &serialize_fields(fields), ConfigFormat::Android, !IS_ROOT)
            .unwrap_err();
    }

    #[test]
    fn inconsistent_root_authority_hash_size() {
        let mut fields = valid_payload_fields();
        fields.insert(AUTHORITY_HASH, Value::Bytes(vec![1; 20]));
        let session = Session { options: Options::default() };
        Payload::from_cbor(&session, &serialize_fields(fields), ConfigFormat::Android, IS_ROOT)
            .unwrap();
    }

    #[test]
    fn inconsistent_root_authority_hash_size_auth_differ_unexcepted() {
        let mut fields = valid_payload_fields();
        fields.insert(AUTHORITY_HASH, Value::Bytes(vec![1; 20]));
        let entries = encode_fields(fields);
        let profile = Profile { allow_root_varied_auth_hash_size: false, ..Profile::default() };
        Payload::from_entries(&profile, entries, ConfigFormat::Android, IS_ROOT, !ALLOW_ANY_MODE)
            .unwrap_err();
    }

    #[test]
    fn bad_config_hash_size() {
        let mut fields = valid_payload_fields();
        fields.insert(CONFIG_HASH, Value::Bytes(vec![1; 16]));
        let session = Session { options: Options::default() };
        Payload::from_cbor(&session, &serialize_fields(fields), ConfigFormat::Android, !IS_ROOT)
            .unwrap_err();
    }

    #[test]
    fn inconsistent_config_hash_size() {
        let mut fields = valid_payload_fields();
        fields.insert(CODE_HASH, Value::Bytes(vec![1; 32]));
        fields.insert(AUTHORITY_HASH, Value::Bytes(vec![1; 32]));
        let session = Session { options: Options::default() };
        Payload::from_cbor(&session, &serialize_fields(fields), ConfigFormat::Android, !IS_ROOT)
            .unwrap_err();
    }

    #[test]
    fn inconsistent_root_config_hash_size() {
        let mut fields = valid_payload_fields();
        fields.insert(CODE_HASH, Value::Bytes(vec![1; 32]));
        fields.insert(AUTHORITY_HASH, Value::Bytes(vec![1; 32]));
        let session = Session { options: Options::default() };
        Payload::from_cbor(&session, &serialize_fields(fields), ConfigFormat::Android, IS_ROOT)
            .unwrap_err();
    }

    #[test]
    fn inconsistent_root_config_hash_size_auth_differ_unexcepted() {
        let mut fields = valid_payload_fields();
        fields.insert(CODE_HASH, Value::Bytes(vec![1; 32]));
        fields.insert(AUTHORITY_HASH, Value::Bytes(vec![1; 32]));
        let entries = encode_fields(fields);
        let profile = Profile { allow_root_varied_auth_hash_size: false, ..Profile::default() };
        Payload::from_entries(&profile, entries, ConfigFormat::Android, IS_ROOT, !ALLOW_ANY_MODE)
            .unwrap_err();
    }

    #[test]
    fn mode_not_configured() {
        let mut fields = valid_payload_fields();
        fields.insert(MODE, Value::Bytes(vec![0]));
        let mut session = Session { options: Options::default() };
        let serialized_fields = serialize_fields(fields);
        Payload::from_cbor(&session, &serialized_fields, ConfigFormat::Android, !IS_ROOT)
            .unwrap_err();
        session.set_allow_any_mode(true);
        let payload =
            Payload::from_cbor(&session, &serialized_fields, ConfigFormat::Android, !IS_ROOT)
                .unwrap();
        assert_eq!(payload.mode(), DiceMode::NotConfigured);
    }

    #[test]
    fn mode_not_configured_degenerate() {
        let mut fields = valid_payload_fields();
        fields.insert(MODE, Value::Bytes(vec![0]));
        let session = Session { options: Options::default() };
        let payload = PayloadFields::from_cbor(
            &session,
            &serialize_fields(fields),
            ConfigFormat::Android,
            !IS_ROOT,
            POSSIBLY_DEGENERATE,
        )
        .unwrap();
        assert_eq!(payload.mode.unwrap(), DiceMode::NotConfigured);
    }

    #[test]
    fn mode_normal() {
        let mut fields = valid_payload_fields();
        fields.insert(MODE, Value::Bytes(vec![1]));
        let session = Session { options: Options::default() };
        let payload = Payload::from_cbor(
            &session,
            &serialize_fields(fields),
            ConfigFormat::Android,
            !IS_ROOT,
        )
        .unwrap();
        assert_eq!(payload.mode(), DiceMode::Normal);
    }

    #[test]
    fn mode_normal_root() {
        let mut fields = valid_payload_fields();
        fields.insert(MODE, Value::Bytes(vec![1]));
        let session = Session { options: Options::default() };
        let payload =
            Payload::from_cbor(&session, &serialize_fields(fields), ConfigFormat::Android, IS_ROOT)
                .unwrap();
        assert_eq!(payload.mode(), DiceMode::Normal);
    }

    #[test]
    fn mode_normal_root_debug_unexcepted() {
        let mut fields = valid_payload_fields();
        fields.insert(MODE, Value::Bytes(vec![1]));
        let entries = encode_fields(fields);
        let profile = Profile { allow_root_mode_debug: false, ..Profile::default() };
        Payload::from_entries(&profile, entries, ConfigFormat::Android, IS_ROOT, !ALLOW_ANY_MODE)
            .unwrap();
    }

    #[test]
    fn mode_debug() {
        let mut fields = valid_payload_fields();
        fields.insert(MODE, Value::Bytes(vec![2]));
        let mut session = Session { options: Options::default() };
        let serialized_fields = serialize_fields(fields);
        Payload::from_cbor(&session, &serialized_fields, ConfigFormat::Android, !IS_ROOT)
            .unwrap_err();
        session.set_allow_any_mode(true);
        let payload =
            Payload::from_cbor(&session, &serialized_fields, ConfigFormat::Android, !IS_ROOT)
                .unwrap();
        assert_eq!(payload.mode(), DiceMode::Debug);
    }

    #[test]
    fn mode_debug_root() {
        let mut fields = valid_payload_fields();
        fields.insert(MODE, Value::Bytes(vec![2]));
        let session = Session { options: Options::default() };
        let payload =
            Payload::from_cbor(&session, &serialize_fields(fields), ConfigFormat::Android, IS_ROOT)
                .unwrap();
        assert_eq!(payload.mode(), DiceMode::Debug);
    }

    #[test]
    fn mode_debug_root_debug_unexcepted() {
        let mut fields = valid_payload_fields();
        fields.insert(MODE, Value::Bytes(vec![2]));
        let entries = encode_fields(fields);
        let profile = Profile { allow_root_mode_debug: false, ..Profile::default() };
        Payload::from_entries(&profile, entries, ConfigFormat::Android, IS_ROOT, !ALLOW_ANY_MODE)
            .unwrap_err();
    }

    #[test]
    fn mode_recovery() {
        let mut fields = valid_payload_fields();
        fields.insert(MODE, Value::Bytes(vec![3]));
        let mut session = Session { options: Options::default() };
        let serialized_fields = serialize_fields(fields);
        Payload::from_cbor(&session, &serialized_fields, ConfigFormat::Android, !IS_ROOT)
            .unwrap_err();
        session.set_allow_any_mode(true);
        let payload =
            Payload::from_cbor(&session, &serialized_fields, ConfigFormat::Android, !IS_ROOT)
                .unwrap();
        assert_eq!(payload.mode(), DiceMode::Recovery);
    }

    #[test]
    fn mode_recovery_root() {
        let mut fields = valid_payload_fields();
        fields.insert(MODE, Value::Bytes(vec![3]));
        let session = Session { options: Options::default() };
        Payload::from_cbor(&session, &serialize_fields(fields), ConfigFormat::Android, IS_ROOT)
            .unwrap_err();
    }

    #[test]
    fn mode_invalid_becomes_not_configured() {
        let mut fields = valid_payload_fields();
        fields.insert(MODE, Value::Bytes(vec![4]));
        let mut session = Session { options: Options::default() };
        session.set_allow_any_mode(true);
        let payload = Payload::from_cbor(
            &session,
            &serialize_fields(fields),
            ConfigFormat::Android,
            !IS_ROOT,
        )
        .unwrap();
        assert_eq!(payload.mode(), DiceMode::NotConfigured);
    }

    #[test]
    fn mode_multiple_bytes() {
        let mut fields = valid_payload_fields();
        fields.insert(MODE, Value::Bytes(vec![0, 1]));
        let session = Session { options: Options::default() };
        Payload::from_cbor(&session, &serialize_fields(fields), ConfigFormat::Android, !IS_ROOT)
            .unwrap_err();
    }

    #[test]
    fn mode_int_debug() {
        let mut fields = valid_payload_fields();
        fields.insert(MODE, Value::from(2));
        let entries = encode_fields(fields);
        Payload::from_entries(
            &Profile::default(),
            entries.clone(),
            ConfigFormat::Android,
            !IS_ROOT,
            ALLOW_ANY_MODE,
        )
        .unwrap_err();
        let profile = Profile { mode_type: ModeType::IntOrBytes, ..Profile::default() };
        let payload = Payload::from_entries(
            &profile,
            entries,
            ConfigFormat::Android,
            !IS_ROOT,
            ALLOW_ANY_MODE,
        )
        .unwrap();
        assert_eq!(payload.mode(), DiceMode::Debug);
    }

    #[test]
    fn subject_public_key_garbage() {
        let mut fields = valid_payload_fields();
        fields.insert(SUBJECT_PUBLIC_KEY, Value::Bytes(vec![17; 64]));
        let session = Session { options: Options::default() };
        Payload::from_cbor(&session, &serialize_fields(fields), ConfigFormat::Android, !IS_ROOT)
            .unwrap_err();
    }

    #[test]
    fn key_usage_little_endian() {
        let mut fields = valid_payload_fields();
        fields.insert(KEY_USAGE, Value::Bytes(vec![0x20, 0x00, 0x00]));
        let cbor = serialize_fields(fields);
        let session = Session { options: Options::default() };
        Payload::from_cbor(&session, &cbor, ConfigFormat::Android, !IS_ROOT).unwrap();
    }

    #[test]
    fn key_usage_little_endian_invalid() {
        let mut fields = valid_payload_fields();
        fields.insert(KEY_USAGE, Value::Bytes(vec![0x20, 0xbe, 0xef]));
        let cbor = serialize_fields(fields);
        let session = Session { options: Options::default() };
        Payload::from_cbor(&session, &cbor, ConfigFormat::Android, !IS_ROOT).unwrap_err();
    }

    #[test]
    fn key_usage_big_endian() {
        let mut fields = valid_payload_fields();
        fields.insert(KEY_USAGE, Value::Bytes(vec![0x00, 0x20]));
        let entries = encode_fields(fields);
        Payload::from_entries(
            &Profile::default(),
            entries.clone(),
            ConfigFormat::Android,
            false,
            false,
        )
        .unwrap_err();
        let profile = Profile { allow_big_endian_key_usage: true, ..Profile::default() };
        Payload::from_entries(&profile, entries, ConfigFormat::Android, !IS_ROOT, !ALLOW_ANY_MODE)
            .unwrap();
    }

    #[test]
    fn key_usage_big_endian_invalid() {
        let mut fields = valid_payload_fields();
        fields.insert(KEY_USAGE, Value::Bytes(vec![0x00, 0xfe, 0x20]));
        let entries = encode_fields(fields);
        Payload::from_entries(
            &Profile::default(),
            entries.clone(),
            ConfigFormat::Android,
            false,
            false,
        )
        .unwrap_err();
        let profile = Profile { allow_big_endian_key_usage: true, ..Profile::default() };
        Payload::from_entries(&profile, entries, ConfigFormat::Android, !IS_ROOT, !ALLOW_ANY_MODE)
            .unwrap_err();
    }

    #[test]
    fn key_usage_invalid() {
        let mut fields = valid_payload_fields();
        fields.insert(KEY_USAGE, Value::Bytes(vec![0x00, 0x10]));
        let entries = encode_fields(fields);
        Payload::from_entries(
            &Profile::default(),
            entries.clone(),
            ConfigFormat::Android,
            false,
            false,
        )
        .unwrap_err();
        let profile = Profile { allow_big_endian_key_usage: true, ..Profile::default() };
        Payload::from_entries(&profile, entries, ConfigFormat::Android, !IS_ROOT, !ALLOW_ANY_MODE)
            .unwrap_err();
    }

    #[test]
    fn key_usage_empty() {
        let mut fields = valid_payload_fields();
        fields.insert(KEY_USAGE, Value::Bytes(vec![]));
        let entries = encode_fields(fields);
        Payload::from_entries(
            &Profile::default(),
            entries.clone(),
            ConfigFormat::Android,
            false,
            false,
        )
        .unwrap_err();
        let profile = Profile { allow_big_endian_key_usage: true, ..Profile::default() };
        Payload::from_entries(&profile, entries, ConfigFormat::Android, !IS_ROOT, !ALLOW_ANY_MODE)
            .unwrap_err();
    }

    #[test]
    fn config_desc_custom_field_above() {
        let mut fields = valid_payload_fields();
        let config_desc = serialize(cbor!({-69999 => "custom"}).unwrap());
        let config_hash = sha512(&config_desc).to_vec();
        fields.insert(CONFIG_DESC, Value::Bytes(config_desc));
        fields.insert(CONFIG_HASH, Value::Bytes(config_hash));
        let session = Session { options: Options::default() };
        Payload::from_cbor(&session, &serialize_fields(fields), ConfigFormat::Android, !IS_ROOT)
            .unwrap();
    }

    #[test]
    fn config_desc_reserved_field_max() {
        let mut fields = valid_payload_fields();
        let config_desc = serialize(cbor!({-70000 => "reserved"}).unwrap());
        let config_hash = sha512(&config_desc).to_vec();
        fields.insert(CONFIG_DESC, Value::Bytes(config_desc));
        fields.insert(CONFIG_HASH, Value::Bytes(config_hash));
        let session = Session { options: Options::default() };
        Payload::from_cbor(&session, &serialize_fields(fields), ConfigFormat::Android, !IS_ROOT)
            .unwrap_err();
    }

    #[test]
    fn config_desc_reserved_field_min() {
        let mut fields = valid_payload_fields();
        let config_desc = serialize(cbor!({-70999 => "reserved"}).unwrap());
        let config_hash = sha512(&config_desc).to_vec();
        fields.insert(CONFIG_DESC, Value::Bytes(config_desc));
        fields.insert(CONFIG_HASH, Value::Bytes(config_hash));
        let session = Session { options: Options::default() };
        Payload::from_cbor(&session, &serialize_fields(fields), ConfigFormat::Android, !IS_ROOT)
            .unwrap_err();
    }

    #[test]
    fn config_desc_custom_field_below() {
        let mut fields = valid_payload_fields();
        let config_desc = serialize(cbor!({-71000 => "custom"}).unwrap());
        let config_hash = sha512(&config_desc).to_vec();
        fields.insert(CONFIG_DESC, Value::Bytes(config_desc));
        fields.insert(CONFIG_HASH, Value::Bytes(config_hash));
        let session = Session { options: Options::default() };
        Payload::from_cbor(&session, &serialize_fields(fields), ConfigFormat::Android, !IS_ROOT)
            .unwrap();
    }

    #[test]
    fn config_desc_custom_fields() -> anyhow::Result<()> {
        let mut fields = valid_payload_fields();
        let config_desc = serialize(cbor!({-71000 => "custom hi", -69999 => "custom lo"})?);
        let config_hash = sha512(&config_desc).to_vec();
        fields.insert(CONFIG_DESC, Value::Bytes(config_desc));
        fields.insert(CONFIG_HASH, Value::Bytes(config_hash));
        let session = Session { options: Options::default() };
        let payload = Payload::from_cbor(
            &session,
            &serialize_fields(fields),
            ConfigFormat::Android,
            !IS_ROOT,
        )?;
        let extensions = payload.config_desc().extensions();
        let extensions = HashMap::<_, _>::from_iter(extensions.to_owned());

        assert_eq!(extensions.get(&-71000).unwrap(), &serialize(cbor!("custom hi")?));
        assert_eq!(extensions.get(&-69999).unwrap(), &serialize(cbor!("custom lo")?));
        assert_eq!(extensions.len(), 2);

        Ok(())
    }

    #[test]
    fn config_desc_not_android_spec() {
        let mut fields = valid_payload_fields();
        fields.insert(CONFIG_DESC, Value::Bytes(vec![0xcd; 64]));
        let cbor = serialize_fields(fields);
        let session = Session { options: Options::default() };
        Payload::from_cbor(&session, &cbor, ConfigFormat::Android, false).unwrap_err();
        let payload =
            Payload::from_cbor(&session, &cbor, ConfigFormat::AndroidOrIgnored, !IS_ROOT).unwrap();
        assert_eq!(payload.config_desc(), &ConfigDesc::default());
    }

    #[test]
    fn config_desc_component_instance_name() {
        let mut fields = valid_payload_fields();
        let config_desc = serialize(cbor!({COMPONENT_INSTANCE_NAME => "foobar"}).unwrap());
        let config_hash = sha512(&config_desc).to_vec();
        fields.insert(CONFIG_DESC, Value::Bytes(config_desc));
        fields.insert(CONFIG_HASH, Value::Bytes(config_hash));
        let cbor = serialize_fields(fields);
        let session = Session { options: Options::default() };
        let payload = Payload::from_cbor(&session, &cbor, ConfigFormat::Android, !IS_ROOT).unwrap();
        assert_eq!(payload.config_desc().component_instance_name(), Some("foobar"));
    }

    #[test]
    fn config_desc_component_version_string() {
        let mut fields = valid_payload_fields();
        let config_desc = serialize(
            cbor!({COMPONENT_VERSION => "It's version 4", SECURITY_VERSION => 99999999}).unwrap(),
        );
        let config_hash = sha512(&config_desc).to_vec();
        fields.insert(CONFIG_DESC, Value::Bytes(config_desc));
        fields.insert(CONFIG_HASH, Value::Bytes(config_hash));
        let entries = encode_fields(fields);
        let profile =
            Profile { component_version_type: ComponentVersionType::Int, ..Profile::default() };
        Payload::from_entries(
            &profile,
            entries.clone(),
            ConfigFormat::Android,
            !IS_ROOT,
            !ALLOW_ANY_MODE,
        )
        .unwrap_err();
        let payload = Payload::from_entries(
            &Profile::default(),
            entries,
            ConfigFormat::Android,
            false,
            false,
        )
        .unwrap();
        assert_eq!(
            payload.config_desc().component_version(),
            Some(&ComponentVersion::String("It's version 4".to_string()))
        );
    }

    #[test]
    fn config_desc_security_version() {
        let mut fields = valid_payload_fields();
        let config_desc = serialize(cbor!({SECURITY_VERSION => 0x12345678}).unwrap());
        let config_hash = sha512(&config_desc).to_vec();
        fields.insert(CONFIG_DESC, Value::Bytes(config_desc));
        fields.insert(CONFIG_HASH, Value::Bytes(config_hash));
        let cbor = serialize_fields(fields);
        let session = Session { options: Options::default() };
        let payload = Payload::from_cbor(&session, &cbor, ConfigFormat::Android, !IS_ROOT).unwrap();
        assert_eq!(payload.config_desc().security_version(), Some(0x12345678));
    }

    #[test]
    fn config_desc_security_version_omitted() {
        let mut fields = valid_payload_fields();
        let config_desc = serialize(cbor!({}).unwrap());
        let config_hash = sha512(&config_desc).to_vec();
        fields.insert(CONFIG_DESC, Value::Bytes(config_desc));
        fields.insert(CONFIG_HASH, Value::Bytes(config_hash));
        let entries = encode_fields(fields);
        Payload::from_entries(
            &Profile::default(),
            entries.clone(),
            ConfigFormat::Android,
            false,
            false,
        )
        .unwrap_err();
        let profile = Profile { security_version_optional: true, ..Profile::default() };
        let payload = Payload::from_entries(
            &profile,
            entries,
            ConfigFormat::Android,
            !IS_ROOT,
            !ALLOW_ANY_MODE,
        )
        .unwrap();
        assert_eq!(payload.config_desc().security_version(), None);
    }

    #[test]
    fn config_desc_security_version_fixed_size_encoding() {
        let mut fields = valid_payload_fields();
        let config_desc = vec![
            0xa1, // Map of one element.
            0x3a, 0x00, 0x01, 0x11, 0x74, // SECURITY_VERSION.
            0x1a, 0x00, 0x00, 0xca, 0xfe, // Non-deterministic encoding of 0xcafe.
        ];
        let config_hash = sha512(&config_desc).to_vec();
        fields.insert(CONFIG_DESC, Value::Bytes(config_desc));
        fields.insert(CONFIG_HASH, Value::Bytes(config_hash));
        let cbor = serialize_fields(fields);
        let session = Session { options: Options::default() };
        let payload = Payload::from_cbor(&session, &cbor, ConfigFormat::Android, !IS_ROOT).unwrap();
        assert_eq!(payload.config_desc().security_version(), Some(0xcafe));
    }

    #[test]
    fn config_desc_security_version_negative() {
        let mut fields = valid_payload_fields();
        let config_desc = serialize(cbor!({SECURITY_VERSION => Value::from(-12)}).unwrap());
        fields.insert(CONFIG_DESC, Value::Bytes(config_desc));
        let cbor = serialize_fields(fields);
        let session = Session { options: Options::default() };
        Payload::from_cbor(&session, &cbor, ConfigFormat::Android, !IS_ROOT).unwrap_err();
    }

    #[test]
    fn config_desc_resettable() {
        let mut fields = valid_payload_fields();
        let config_desc = serialize(cbor!({RESETTABLE => null}).unwrap());
        let config_hash = sha512(&config_desc).to_vec();
        fields.insert(CONFIG_DESC, Value::Bytes(config_desc));
        fields.insert(CONFIG_HASH, Value::Bytes(config_hash));
        let cbor = serialize_fields(fields);
        let session = Session { options: Options::default() };
        let payload = Payload::from_cbor(&session, &cbor, ConfigFormat::Android, !IS_ROOT).unwrap();
        assert!(payload.config_desc().resettable());
    }

    #[test]
    fn config_desc_rkp_vm_marker() {
        let mut fields = valid_payload_fields();
        let config_desc = serialize(cbor!({RKP_VM_MARKER => null}).unwrap());
        let config_hash = sha512(&config_desc).to_vec();
        fields.insert(CONFIG_DESC, Value::Bytes(config_desc));
        fields.insert(CONFIG_HASH, Value::Bytes(config_hash));
        let cbor = serialize_fields(fields);
        let session = Session { options: Options::default() };
        let payload = Payload::from_cbor(&session, &cbor, ConfigFormat::Android, !IS_ROOT).unwrap();
        assert!(payload.config_desc().rkp_vm_marker());
    }

    #[test]
    fn config_desc_nulls_omitted() {
        let mut fields = valid_payload_fields();
        let config_desc = serialize(cbor!({}).unwrap());
        let config_hash = sha512(&config_desc).to_vec();
        fields.insert(CONFIG_DESC, Value::Bytes(config_desc));
        fields.insert(CONFIG_HASH, Value::Bytes(config_hash));
        let cbor = serialize_fields(fields);
        let session = Session { options: Options::default() };
        let payload = Payload::from_cbor(&session, &cbor, ConfigFormat::Android, !IS_ROOT).unwrap();
        assert!(!payload.config_desc().resettable());
        assert!(!payload.config_desc().rkp_vm_marker());
    }

    #[test]
    fn config_hash_missing() {
        let mut fields = valid_payload_fields();
        fields.remove(&CONFIG_HASH);
        let entries = encode_fields(fields);
        Payload::from_entries(
            &Profile::default(),
            entries,
            ConfigFormat::Android,
            !IS_ROOT,
            !ALLOW_ANY_MODE,
        )
        .unwrap_err();
    }

    #[test]
    fn integer_key_ops() {
        let mut fields = valid_payload_fields();
        let subject_public_key = cbor!({
            iana::KeyParameter::Kty.to_i64() => iana::KeyType::OKP.to_i64(),
            iana::KeyParameter::Alg.to_i64() => iana::Algorithm::EdDSA.to_i64(),
            iana::KeyParameter::KeyOps.to_i64() => iana::KeyOperation::Verify.to_i64(),
            iana::OkpKeyParameter::Crv.to_i64() => iana::EllipticCurve::Ed25519.to_i64(),
            iana::OkpKeyParameter::X.to_i64() => Value::Bytes(vec![0; 32]),
        })
        .unwrap();
        fields.insert(SUBJECT_PUBLIC_KEY, Value::Bytes(serialize(subject_public_key)));
        let entries = encode_fields(fields);
        Payload::from_entries(
            &Profile::default(),
            entries.clone(),
            ConfigFormat::Android,
            false,
            false,
        )
        .unwrap_err();
        let profile = Profile { key_ops_type: KeyOpsType::IntOrArray, ..Profile::default() };
        Payload::from_entries(&profile, entries, ConfigFormat::Android, !IS_ROOT, !ALLOW_ANY_MODE)
            .unwrap();
    }

    #[test]
    fn extract_profile_version_named_profiles() {
        let test_cases = [
            ("android.14", ProfileVersion::Android14),
            ("android.15", ProfileVersion::Android15),
            ("android.16", ProfileVersion::Android16),
        ];
        for (profile_name, expected_version) in test_cases {
            let mut fields = valid_payload_fields();
            fields.insert(PROFILE_NAME, Value::from(profile_name));
            let entries = encode_fields(fields);
            let session = Session {
                options: Options {
                    dice_profile_range: DiceProfileRange::new(expected_version, expected_version),
                    ..Default::default()
                },
            };
            let profile_version =
                PayloadFields::extract_profile_version(&session, &entries).unwrap();
            assert_eq!(profile_version, expected_version);
        }
    }

    #[test]
    fn extract_profile_version_named_android_13_fails() {
        let session = Session {
            options: Options {
                dice_profile_range: DiceProfileRange::new(
                    ProfileVersion::Android13,
                    ProfileVersion::Android16,
                ),
                ..Default::default()
            },
        };
        let mut fields = valid_payload_fields();
        fields.insert(PROFILE_NAME, Value::from("android.13"));
        let entries = encode_fields(fields);
        PayloadFields::extract_profile_version(&session, &entries).unwrap_err();
    }

    #[test]
    fn extract_profile_version_multiple_profile_name_entries_fails() {
        let session = Session {
            options: Options {
                dice_profile_range: DiceProfileRange::new(
                    ProfileVersion::Android13,
                    ProfileVersion::Android16,
                ),
                ..Default::default()
            },
        };
        let mut fields = valid_payload_fields();
        fields.insert(PROFILE_NAME, Value::from("android.15"));
        let mut entries = encode_fields(fields);
        entries.push((Value::from(PROFILE_NAME), Value::from("android.15")));
        PayloadFields::extract_profile_version(&session, &entries).unwrap_err();
    }

    #[test]
    fn extract_profile_version_out_of_range_fails() {
        let session = Session {
            options: Options {
                dice_profile_range: DiceProfileRange::new(
                    ProfileVersion::Android15,
                    ProfileVersion::Android15,
                ),
                ..Default::default()
            },
        };
        let mut fields = valid_payload_fields();
        fields.insert(PROFILE_NAME, Value::from("android.14"));
        let entries = encode_fields(fields.clone());
        PayloadFields::extract_profile_version(&session, &entries).unwrap_err();
        fields.insert(PROFILE_NAME, Value::from("android.16"));
        let entries = encode_fields(fields);
        PayloadFields::extract_profile_version(&session, &entries).unwrap_err();
    }

    #[test]
    fn extract_profile_version_default_when_not_named_up_to_android_14() {
        let entries = encode_fields(valid_payload_fields());
        for expected_version in [ProfileVersion::Android13, ProfileVersion::Android14] {
            let session = Session {
                options: Options {
                    dice_profile_range: DiceProfileRange::new(
                        expected_version,
                        ProfileVersion::Android16,
                    ),
                    ..Default::default()
                },
            };
            let profile_version =
                PayloadFields::extract_profile_version(&session, &entries).unwrap();
            assert_eq!(profile_version, expected_version);
        }
    }

    #[test]
    fn extract_profile_version_named_profile_required_from_android_15() {
        let entries = encode_fields(valid_payload_fields());
        for min_version in [ProfileVersion::Android15, ProfileVersion::Android16] {
            let session = Session {
                options: Options {
                    dice_profile_range: DiceProfileRange::new(
                        min_version,
                        ProfileVersion::Android16,
                    ),
                    ..Default::default()
                },
            };
            PayloadFields::extract_profile_version(&session, &entries).unwrap_err();
        }
    }

    fn valid_payload_fields() -> HashMap<i64, Value> {
        let key = PrivateKey::from_pem(ED25519_KEY_PEM[0]).public_key();
        let subject_public_key = key.to_cose_key().unwrap().to_vec().unwrap();
        let config_desc = serialize(
            cbor!({COMPONENT_NAME => "component name", SECURITY_VERSION => 1234}).unwrap(),
        );
        let config_hash = sha512(&config_desc).to_vec();
        HashMap::from([
            (ISS, Value::from("issuer")),
            (SUB, Value::from("subject")),
            (SUBJECT_PUBLIC_KEY, Value::Bytes(subject_public_key)),
            (KEY_USAGE, Value::Bytes(vec![0x20])),
            (CODE_HASH, Value::Bytes(vec![1; 64])),
            (CONFIG_DESC, Value::Bytes(config_desc)),
            (CONFIG_HASH, Value::Bytes(config_hash)),
            (AUTHORITY_HASH, Value::Bytes(vec![2; 64])),
            (MODE, Value::Bytes(vec![1])),
        ])
    }

    fn encode_fields(mut fields: HashMap<i64, Value>) -> Vec<(Value, Value)> {
        fields.drain().map(|(k, v)| (Value::from(k), v)).collect()
    }

    fn serialize_fields(fields: HashMap<i64, Value>) -> Vec<u8> {
        serialize(Value::Map(encode_fields(fields)))
    }
}
