//! This library provides bindings for C++ code to comfortably and reasonably safely interface with
//! the libhwtrust Rust library.

use coset::CborSerializable;
use hwtrust::dice::ChainForm;
use hwtrust::dice::DiceMode;
use hwtrust::dice::ProfileVersion;
use hwtrust::rkp::Csr as InnerCsr;
use hwtrust::session::{DiceProfileRange, Options, RkpInstance, Session};
use std::str::FromStr;

/// Since the AVF DICE chain combines both vendor and AOSP DICE chains, the chain doesn't rely
/// solely on the VSR for vendors, unlike pure vendor DICE chains. This constant defines the
/// minimum profile version required for the AOSP/AVF portion of the DICE chain.
///
/// Since the AVF portion follows the vendor portion, its version is always higher.
const AVF_DICE_PROFILE_VERSION: ProfileVersion = ProfileVersion::Android16;

#[allow(clippy::needless_maybe_sized)]
#[allow(unsafe_op_in_unsafe_fn)]
#[cxx::bridge(namespace = "hwtrust::rust")]
mod ffi {
    /// The set of validation rules to apply.
    enum DiceChainKind {
        /// The DICE chain specified by VSR 13.
        Vsr13,
        /// The DICE chain specified by VSR 14.
        Vsr14,
        /// The DICE chain specified by VSR 15.
        Vsr15,
        /// The DICE chain specified by VSR 16.
        Vsr16,
    }

    /// The result type used by [`verify_dice_chain()`]. The standard [`Result`] is currently only
    /// converted to exceptions by `cxxbridge` but we can't use exceptions so need to do something
    /// custom.
    struct VerifyDiceChainResult {
        /// If non-empty, the description of the verification error that occurred.
        error: String,
        /// If [`error`] is empty, a handle to the verified chain.
        chain: Box<DiceChain>,
        /// If [`error`] is empty, the length of the chain.
        len: usize,
    }

    /// The result type used by [`validate_csr()`]. The standard [`Result`] is currently only
    /// converted to exceptions by `cxxbridge` but we can't use exceptions so need to do something
    /// custom.
    struct ValidateCsrResult {
        /// If non-empty, the description of the verification error that occurred.
        error: String,
        /// If [`error`] is empty, a handle to the validated Csr.
        csr: Box<Csr>,
    }

    struct BoolResult {
        error: String,
        value: bool,
    }

    extern "Rust" {
        type DiceChain;

        #[cxx_name = VerifyDiceChain]
        fn verify_dice_chain(
            chain: &[u8],
            kind: DiceChainKind,
            allow_any_mode: bool,
            instance: &str,
        ) -> VerifyDiceChainResult;

        #[cxx_name = GetDiceChainPublicKey]
        fn get_dice_chain_public_key(chain: &DiceChain, n: usize) -> Vec<u8>;

        #[cxx_name = compareRootPublicKeyInDiceChain]
        fn compare_root_public_key_in_dice_chain(
            chain1: &DiceChain,
            chain2: &DiceChain,
        ) -> BoolResult;

        #[cxx_name = componentNameInDiceChainContains]
        fn component_name_in_dice_chain_contains(chain: &DiceChain, substring: &str) -> BoolResult;

        #[cxx_name = hasNonNormalModeInDiceChain]
        fn has_non_normal_mode_in_dice_chain(chain: &DiceChain) -> BoolResult;

        #[cxx_name = IsDiceChainProper]
        fn is_dice_chain_proper(chain: &DiceChain) -> bool;

        type Csr;

        #[cxx_name = validateCsr]
        fn validate_csr(
            csr: &[u8],
            kind: DiceChainKind,
            is_factory: bool,
            allow_any_mode: bool,
            instance: &str,
        ) -> ValidateCsrResult;

        #[cxx_name = getDiceChainFromCsr]
        fn get_dice_chain_from_csr(csr: &Csr) -> VerifyDiceChainResult;

        #[cxx_name = csrHasUdsCerts]
        fn csr_has_uds_certs(csr: &Csr) -> bool;

        #[cxx_name = getCsrPayloadFromCsr]
        fn get_csr_payload_from_csr(csr: &Csr) -> Vec<u8>;

        #[cxx_name = compareKeysToSignInCsr]
        fn compare_keys_to_sign_in_csr(csr: &Csr, keys_to_sign: &[u8]) -> BoolResult;

        #[cxx_name = compareChallengeInCsr]
        fn compare_challenge_in_csr(csr: &Csr, challenge: &[u8]) -> BoolResult;
    }
}

impl TryInto<Options> for ffi::DiceChainKind {
    type Error = String;

    fn try_into(self) -> Result<Options, Self::Error> {
        match self {
            ffi::DiceChainKind::Vsr13 => Ok(Options::vsr13()),
            ffi::DiceChainKind::Vsr14 => Ok(Options::vsr14()),
            ffi::DiceChainKind::Vsr15 => Ok(Options::vsr15()),
            ffi::DiceChainKind::Vsr16 => Ok(Options::vsr16()),
            _ => Err("invalid chain kind".to_string()),
        }
    }
}

/// A DICE chain as exposed over the cxx bridge.
pub struct DiceChain(Option<ChainForm>);

fn new_session(
    kind: ffi::DiceChainKind,
    allow_any_mode: bool,
    instance: &str,
) -> Result<Session, String> {
    let mut options: Options = kind.try_into()?;
    let Ok(rkp_instance) = RkpInstance::from_str(instance) else {
        return Err(format!("invalid RKP instance: {}", instance));
    };
    if rkp_instance == RkpInstance::Avf {
        options.dice_profile_range =
            DiceProfileRange::new(options.dice_profile_range.start(), AVF_DICE_PROFILE_VERSION)
    }
    let mut session = Session { options };
    session.set_rkp_instance(rkp_instance);
    session.set_allow_any_mode(allow_any_mode);
    Ok(session)
}

fn verify_dice_chain(
    chain: &[u8],
    kind: ffi::DiceChainKind,
    allow_any_mode: bool,
    instance: &str,
) -> ffi::VerifyDiceChainResult {
    let session = match new_session(kind, allow_any_mode, instance) {
        Ok(session) => session,
        Err(e) => {
            return ffi::VerifyDiceChainResult {
                error: e,
                chain: Box::new(DiceChain(None)),
                len: 0,
            }
        }
    };

    match ChainForm::from_cbor(&session, chain) {
        Ok(chain) => {
            let len = chain.length();
            let chain = Box::new(DiceChain(Some(chain)));
            ffi::VerifyDiceChainResult { error: "".to_string(), chain, len }
        }
        Err(e) => {
            let error = format!("{:#}", e);
            ffi::VerifyDiceChainResult { error, chain: Box::new(DiceChain(None)), len: 0 }
        }
    }
}

fn get_dice_chain_public_key(chain: &DiceChain, n: usize) -> Vec<u8> {
    if let DiceChain(Some(chain)) = chain {
        let key = match chain {
            ChainForm::Proper(chain) => chain.payloads()[n].subject_public_key(),
            ChainForm::Degenerate(chain) => chain.public_key(),
        };
        if let Ok(cose_key) = key.to_cose_key() {
            if let Ok(bytes) = cose_key.to_vec() {
                return bytes;
            }
        }
    }
    Vec::new()
}

fn compare_root_public_key_in_dice_chain(
    chain1: &DiceChain,
    chain2: &DiceChain,
) -> ffi::BoolResult {
    match (chain1, chain2) {
        (
            DiceChain(Some(ChainForm::Proper(chain1))),
            DiceChain(Some(ChainForm::Proper(chain2))),
        ) => {
            let equal = chain1.root_public_key() == chain2.root_public_key();
            ffi::BoolResult { error: "".to_string(), value: equal }
        }
        _ => ffi::BoolResult {
            error: "Two proper DICE chains were not provided".to_string(),
            value: false,
        },
    }
}

fn component_name_in_dice_chain_contains(chain: &DiceChain, substring: &str) -> ffi::BoolResult {
    match chain {
        DiceChain(Some(chain)) => match chain {
            ChainForm::Proper(chain) => {
                match chain
                    .payloads()
                    .last()
                    .expect("leaf cert was empty")
                    .config_desc()
                    .component_name()
                {
                    Some(name) => {
                        ffi::BoolResult { error: "".to_string(), value: name.contains(substring) }
                    }
                    None => ffi::BoolResult {
                        error: "component name could not be retrieved".to_string(),
                        value: false,
                    },
                }
            }
            ChainForm::Degenerate(_) => {
                ffi::BoolResult { error: "DICE chain is degenerate".to_string(), value: false }
            }
        },
        _ => ffi::BoolResult { error: "A DICE chain must be provided".to_string(), value: false },
    }
}

fn has_non_normal_mode_in_dice_chain(chain: &DiceChain) -> ffi::BoolResult {
    match chain {
        DiceChain(Some(ChainForm::Proper(chain))) => {
            let has_non_normal_mode =
                chain.payloads().iter().any(|payload| payload.mode() != DiceMode::Normal);
            ffi::BoolResult { error: "".to_string(), value: has_non_normal_mode }
        }
        _ => ffi::BoolResult {
            error: "A proper DICE chain must be provided".to_string(),
            value: false,
        },
    }
}

fn is_dice_chain_proper(chain: &DiceChain) -> bool {
    if let DiceChain(Some(chain)) = chain {
        match chain {
            ChainForm::Proper(_) => true,
            ChainForm::Degenerate(_) => false,
        }
    } else {
        false
    }
}

/// A Csr as exposed over the cxx bridge.
pub struct Csr(Option<InnerCsr>);

fn validate_csr(
    csr: &[u8],
    kind: ffi::DiceChainKind,
    is_factory: bool,
    allow_any_mode: bool,
    instance: &str,
) -> ffi::ValidateCsrResult {
    let mut session = match new_session(kind, allow_any_mode, instance) {
        Ok(session) => session,
        Err(e) => return ffi::ValidateCsrResult { error: e, csr: Box::new(Csr(None)) },
    };
    session.set_is_factory(is_factory);
    match InnerCsr::from_cbor(&session, csr) {
        Ok(csr) => {
            let csr = Box::new(Csr(Some(csr)));
            ffi::ValidateCsrResult { error: "".to_string(), csr }
        }
        Err(e) => {
            let error = format!("{:#}", e);
            ffi::ValidateCsrResult { error, csr: Box::new(Csr(None)) }
        }
    }
}

fn get_dice_chain_from_csr(csr: &Csr) -> ffi::VerifyDiceChainResult {
    match csr {
        Csr(Some(csr)) => {
            let chain = csr.dice_chain();
            let len = chain.length();
            let chain = Box::new(DiceChain(Some(chain)));
            ffi::VerifyDiceChainResult { error: "".to_string(), chain, len }
        }
        _ => ffi::VerifyDiceChainResult {
            error: "A CSR needs to be provided".to_string(),
            chain: Box::new(DiceChain(None)),
            len: 0,
        },
    }
}

fn csr_has_uds_certs(csr: &Csr) -> bool {
    match csr {
        Csr(Some(csr)) => csr.has_uds_certs(),
        _ => false,
    }
}

fn get_csr_payload_from_csr(csr: &Csr) -> Vec<u8> {
    match csr {
        Csr(Some(csr)) => csr.csr_payload(),
        _ => Vec::new(),
    }
}

fn compare_keys_to_sign_in_csr(csr: &Csr, keys_to_sign: &[u8]) -> ffi::BoolResult {
    match csr {
        Csr(Some(csr)) => {
            ffi::BoolResult { error: "".to_string(), value: csr.compare_keys_to_sign(keys_to_sign) }
        }
        _ => {
            ffi::BoolResult { error: "KeysToSign could not be compared".to_string(), value: false }
        }
    }
}

fn compare_challenge_in_csr(csr: &Csr, challenge: &[u8]) -> ffi::BoolResult {
    match csr {
        Csr(Some(csr)) => {
            ffi::BoolResult { error: "".to_string(), value: challenge == csr.challenge() }
        }
        _ => ffi::BoolResult { error: "challenge could not be compared".to_string(), value: false },
    }
}
