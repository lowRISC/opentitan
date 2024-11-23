// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::Result;
use cryptoki::session::Session;

use crate::util::attribute::{AttrData, AttributeError, AttributeMap, AttributeType, ObjectClass};
use crate::util::helper;

#[derive(Clone, Debug, Default)]
pub struct ElementaryFile {
    pub name: String,
    pub application: Option<String>,
    pub private: bool,
}

impl ElementaryFile {
    pub fn new(name: String) -> Self {
        Self {
            name,
            ..Default::default()
        }
    }

    pub fn application(mut self, app: String) -> Self {
        self.application = Some(app);
        self
    }

    pub fn private(mut self, private: bool) -> Self {
        self.private = private;
        self
    }

    pub fn find(session: &Session, search: AttributeMap) -> Result<Vec<Self>> {
        let mut search = search;
        search.insert(
            AttributeType::Class,
            AttrData::ObjectClass(ObjectClass::Data),
        );
        let search = search.to_vec()?;
        let attr = [
            AttributeType::Label,
            AttributeType::Application,
            AttributeType::Private,
        ];
        let attr = attr
            .iter()
            .map(|&a| Ok(a.try_into()?))
            .collect::<Result<Vec<cryptoki::object::AttributeType>>>()?;

        let mut result = Vec::new();
        for object in session.find_objects(&search)? {
            let data = session.get_attributes(object, &attr)?;
            let data = AttributeMap::from(data.as_slice());
            result.push(Self {
                name: data
                    .get(&AttributeType::Label)
                    .map(|x| x.try_string())
                    .transpose()?
                    .unwrap_or_else(|| String::from("<unnamed>")),
                application: data
                    .get(&AttributeType::Application)
                    .map(|x| x.try_string())
                    .transpose()?,
                private: data
                    .get(&AttributeType::Private)
                    .map(|x| x.try_into())
                    .transpose()?
                    .unwrap_or(false),
            });
        }
        Ok(result)
    }

    pub fn list(session: &Session) -> Result<Vec<Self>> {
        Self::find(session, AttributeMap::default())
    }

    pub fn exists(self, session: &Session) -> Result<bool> {
        let mut attr = AttributeMap::default();
        attr.insert(
            AttributeType::Class,
            AttrData::ObjectClass(ObjectClass::Data),
        );
        attr.insert(AttributeType::Label, AttrData::Str(self.name.clone()));
        if let Some(app) = &self.application {
            attr.insert(AttributeType::Application, AttrData::Str(app.clone()));
        }
        let attr = attr.to_vec()?;
        let objects = session.find_objects(&attr)?;
        Ok(!objects.is_empty())
    }

    pub fn read(self, session: &Session) -> Result<Vec<u8>> {
        let mut attr = AttributeMap::default();
        attr.insert(
            AttributeType::Class,
            AttrData::ObjectClass(ObjectClass::Data),
        );
        attr.insert(AttributeType::Label, AttrData::Str(self.name.clone()));
        if let Some(app) = &self.application {
            attr.insert(AttributeType::Application, AttrData::Str(app.clone()));
        }
        let attr = attr.to_vec()?;

        let object = helper::find_one_object(session, &attr)?;
        let data = AttributeMap::from_object(session, object)?;
        let value = data
            .get(&AttributeType::Value)
            .ok_or(AttributeError::AttributeNotFound(AttributeType::Value))?;
        let value = Vec::<u8>::try_from(value)?;
        Ok(value)
    }

    pub fn write(self, session: &Session, data: &[u8]) -> Result<()> {
        let mut attr = AttributeMap::default();
        attr.insert(
            AttributeType::Class,
            AttrData::ObjectClass(ObjectClass::Data),
        );
        attr.insert(AttributeType::Label, AttrData::Str(self.name.clone()));
        if let Some(application) = &self.application {
            // Is this a bug in opensc-pkcs11 or in the Nitrokey?
            // It seems the application string needs a nul terminator.
            let mut val = application.clone();
            val.push(0 as char);
            attr.insert(AttributeType::Application, AttrData::Str(val));
        }
        attr.insert(AttributeType::Token, AttrData::from(true));
        attr.insert(AttributeType::Private, AttrData::from(self.private));
        attr.insert(AttributeType::Value, AttrData::from(data));
        let attr = attr.to_vec()?;
        session.create_object(&attr)?;
        Ok(())
    }
}
