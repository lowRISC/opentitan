// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use indexmap::IndexSet;

use crate::template::{
    BasicConstraints, Certificate, CertificateExtension, DiceTcbInfoExtension, DiceTcbInfoFlags,
    EcPublicKey, EcPublicKeyInfo, EcdsaSignature, FirmwareId, KeyUsage, MldsaPublicKeyInfo, Name,
    RawOr, Selectable, Signature, SubjectPublicKeyInfo, Value, Variable,
};

pub trait ListVariables {
    fn list_variables(&self, names: &mut IndexSet<String>);
}

impl<T: ListVariables> ListVariables for Selectable<T> {
    fn list_variables(&self, names: &mut IndexSet<String>) {
        match self {
            Selectable::Value(val) => val.list_variables(names),
            Selectable::Choice(choice) => {
                names.insert(choice.selector.clone());
                for c in &choice.choices {
                    c.list_variables(names);
                }
            }
        }
    }
}

impl<T> ListVariables for Value<T> {
    fn list_variables(&self, names: &mut IndexSet<String>) {
        if let Value::Variable(Variable { name, .. }) = self {
            names.insert(name.clone());
        }
    }
}

impl ListVariables for SubjectPublicKeyInfo {
    fn list_variables(&self, names: &mut IndexSet<String>) {
        match self {
            SubjectPublicKeyInfo::EcPublicKey(ec) => ec.list_variables(names),
            SubjectPublicKeyInfo::Mldsa44(pk)
            | SubjectPublicKeyInfo::Mldsa65(pk)
            | SubjectPublicKeyInfo::Mldsa87(pk) => {
                pk.list_variables(names);
            }
        }
    }
}

impl ListVariables for EcPublicKeyInfo {
    fn list_variables(&self, names: &mut IndexSet<String>) {
        self.public_key.list_variables(names);
    }
}

impl ListVariables for EcPublicKey {
    fn list_variables(&self, names: &mut IndexSet<String>) {
        self.x.list_variables(names);
        self.y.list_variables(names);
    }
}

impl ListVariables for MldsaPublicKeyInfo {
    fn list_variables(&self, names: &mut IndexSet<String>) {
        self.public_key.list_variables(names);
    }
}

impl ListVariables for Signature {
    fn list_variables(&self, names: &mut IndexSet<String>) {
        match self {
            Signature::EcdsaWithSha256 { value } => {
                if let Some(sig) = value {
                    sig.list_variables(names);
                }
            }
            Signature::Mldsa44 { value }
            | Signature::Mldsa65 { value }
            | Signature::Mldsa87 { value } => {
                if let Some(sig) = value {
                    sig.list_variables(names);
                }
            }
        }
    }
}

impl ListVariables for EcdsaSignature {
    fn list_variables(&self, names: &mut IndexSet<String>) {
        self.r.list_variables(names);
        self.s.list_variables(names);
    }
}

impl ListVariables for Name {
    fn list_variables(&self, names: &mut IndexSet<String>) {
        for rdn in self {
            for val in rdn.values() {
                val.list_variables(names);
            }
        }
    }
}

impl ListVariables for BasicConstraints {
    fn list_variables(&self, names: &mut IndexSet<String>) {
        self.ca.list_variables(names);
    }
}

impl ListVariables for KeyUsage {
    fn list_variables(&self, names: &mut IndexSet<String>) {
        if let Some(val) = &self.digital_signature {
            val.list_variables(names);
        }
        if let Some(val) = &self.key_agreement {
            val.list_variables(names);
        }
        if let Some(val) = &self.cert_sign {
            val.list_variables(names);
        }
    }
}

impl ListVariables for CertificateExtension {
    fn list_variables(&self, names: &mut IndexSet<String>) {
        match self {
            CertificateExtension::DiceTcbInfo(dice) => dice.list_variables(names),
        }
    }
}

impl ListVariables for DiceTcbInfoExtension {
    fn list_variables(&self, names: &mut IndexSet<String>) {
        if let Some(val) = &self.model {
            val.list_variables(names);
        }
        if let Some(val) = &self.vendor {
            val.list_variables(names);
        }
        if let Some(val) = &self.version {
            val.list_variables(names);
        }
        if let Some(val) = &self.svn {
            val.list_variables(names);
        }
        if let Some(val) = &self.layer {
            val.list_variables(names);
        }
        if let Some(ids) = &self.fw_ids {
            ids.list_variables(names);
        }
        if let Some(val) = &self.flags {
            val.list_variables(names);
        }
    }
}

impl<T: ListVariables> ListVariables for RawOr<T> {
    fn list_variables(&self, names: &mut IndexSet<String>) {
        match self {
            Self::Type(val) => val.list_variables(names),
            Self::Raw(val) => val.list_variables(names),
        }
    }
}

impl<T: ListVariables> ListVariables for Vec<T> {
    fn list_variables(&self, names: &mut IndexSet<String>) {
        for item in self {
            item.list_variables(names);
        }
    }
}

impl ListVariables for FirmwareId {
    fn list_variables(&self, names: &mut IndexSet<String>) {
        self.digest.list_variables(names);
    }
}

impl ListVariables for DiceTcbInfoFlags {
    fn list_variables(&self, names: &mut IndexSet<String>) {
        self.not_configured.list_variables(names);
        self.not_secure.list_variables(names);
        self.recovery.list_variables(names);
        self.debug.list_variables(names);
    }
}

impl Certificate {
    pub fn list_tbs_variables(&self, names: &mut IndexSet<String>) {
        self.serial_number.list_variables(names);
        self.not_before.list_variables(names);
        self.not_after.list_variables(names);
        self.issuer.list_variables(names);
        self.subject.list_variables(names);
        self.subject_public_key_info.list_variables(names);
        if let Some(val) = &self.authority_key_identifier {
            val.list_variables(names);
        }
        if let Some(val) = &self.subject_key_identifier {
            val.list_variables(names);
        }
        if let Some(val) = &self.basic_constraints {
            val.list_variables(names);
        }
        if let Some(val) = &self.key_usage {
            val.list_variables(names);
        }
        self.subject_alt_name.list_variables(names);
        self.private_extensions.list_variables(names);
        if let Selectable::Choice(choice) = &self.signature {
            names.insert(choice.selector.clone());
        }
    }
}
