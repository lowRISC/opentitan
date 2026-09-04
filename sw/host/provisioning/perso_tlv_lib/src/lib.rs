// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use core::{
    convert::{Into, TryFrom, TryInto},
    iter::Iterator,
    marker::Copy,
    num::TryFromIntError,
};

use arrayvec::ArrayVec;
use perso_tlv_objects::perso_tlv_blob_version_payload;
use ujson_lib::provisioning_data::{PERSO_BLOB_BODY_MAX_SIZE, PersoBlob};

use anyhow::{Result, bail};

// Types of objects which can come from the device in the perso blob.
#[repr(usize)]
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum ObjType {
    UnendorsedX509Cert = perso_tlv_objects::perso_tlv_object_type_kPersoObjectTypeX509Tbs as usize,
    EndorsedX509Cert = perso_tlv_objects::perso_tlv_object_type_kPersoObjectTypeX509Cert as usize,
    DevSeed = perso_tlv_objects::perso_tlv_object_type_kPersoObjectTypeDevSeed as usize,
    EndorsedCwtCert = perso_tlv_objects::perso_tlv_object_type_kPersoObjectTypeCwtCert as usize,
    WasTbsHmac = perso_tlv_objects::perso_tlv_object_type_kPersoObjectTypeWasTbsHmac as usize,
    DeviceId = perso_tlv_objects::perso_tlv_object_type_kPersoObjectTypeDeviceId as usize,
    GenericSeed = perso_tlv_objects::perso_tlv_object_type_kPersoObjectTypeGenericSeed as usize,
    PersoSha256Hash =
        perso_tlv_objects::perso_tlv_object_type_kPersoObjectTypePersoSha256Hash as usize,
    PersoBlobVersion =
        perso_tlv_objects::perso_tlv_object_type_kPersoObjectTypeBlobVersion as usize,
}

pub enum EndorsedCertType {
    EndorsedCwtCert,
    EndorsedX509Cert,
}

impl From<EndorsedCertType> for ObjType {
    fn from(value: EndorsedCertType) -> ObjType {
        match value {
            EndorsedCertType::EndorsedCwtCert => ObjType::EndorsedCwtCert,
            EndorsedCertType::EndorsedX509Cert => ObjType::EndorsedX509Cert,
        }
    }
}

impl TryFrom<ObjType> for u32 {
    type Error = TryFromIntError;
    fn try_from(value: ObjType) -> Result<Self, Self::Error> {
        Self::try_from(value as usize)
    }
}

impl TryFrom<usize> for ObjType {
    type Error = anyhow::Error;

    fn try_from(value: usize) -> Result<Self, Self::Error> {
        const UNENDORSED_X509_CERT: usize = ObjType::UnendorsedX509Cert as usize;
        const ENDORSED_X509_CERT: usize = ObjType::EndorsedX509Cert as usize;
        const DEV_SEED: usize = ObjType::DevSeed as usize;
        const ENDORSED_CWT_CERT: usize = ObjType::EndorsedCwtCert as usize;
        const WAS_TBS_MAC: usize = ObjType::WasTbsHmac as usize;
        const DEVICE_ID: usize = ObjType::DeviceId as usize;
        const GENERIC_SEED: usize = ObjType::GenericSeed as usize;
        const PERSO_SHA256_HASH: usize = ObjType::PersoSha256Hash as usize;
        const PERSO_BLOB_VERSION: usize = ObjType::PersoBlobVersion as usize;

        match value {
            UNENDORSED_X509_CERT => Ok(ObjType::UnendorsedX509Cert),
            ENDORSED_X509_CERT => Ok(ObjType::EndorsedX509Cert),
            DEV_SEED => Ok(ObjType::DevSeed),
            ENDORSED_CWT_CERT => Ok(ObjType::EndorsedCwtCert),
            WAS_TBS_MAC => Ok(ObjType::WasTbsHmac),
            DEVICE_ID => Ok(ObjType::DeviceId),
            GENERIC_SEED => Ok(ObjType::GenericSeed),
            PERSO_SHA256_HASH => Ok(ObjType::PersoSha256Hash),
            PERSO_BLOB_VERSION => Ok(ObjType::PersoBlobVersion),
            _ => bail!("incorrect input value of {value} for ObjType"),
        }
    }
}

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub enum SupportedPersoTlvVersion {
    V0,
    V1,
}

// Header of the LTV object
#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub struct ObjHeader {
    pub obj_size: usize,
    pub obj_type: ObjType,
    pub header_size: usize,
    pub version: SupportedPersoTlvVersion,
}

// Header and body of the certificate payload of the LTV object
pub struct CertWithHeader<'a> {
    // Total size the certificate takes in the buffer, header + hame length +
    // cert size.
    pub wrapped_size: usize,
    pub cert_name: &'a str,
    pub cert_body: Vec<u8>,
}

#[derive(Debug, Clone, Default)]
pub struct PersoBlobBuilder {
    data: ArrayVec<u8, PERSO_BLOB_BODY_MAX_SIZE>,
    num_objs: usize,
}

impl PersoBlobBuilder {
    pub fn new() -> Self {
        Self {
            data: ArrayVec::new(),
            num_objs: 0,
        }
    }

    pub fn push_endorsed_cert(
        &mut self,
        cert_name: &str,
        cert: &Vec<u8>,
        cert_type: EndorsedCertType,
    ) -> Result<()> {
        let version = if cert_name.len() <= PersoTlvTypesV0::MAX_CERT_NAME_LEN
            && cert.len() <= PersoTlvTypesV0::MAX_CERT_LEN
        {
            SupportedPersoTlvVersion::V0
        } else {
            SupportedPersoTlvVersion::V1
        };

        let mut data: Vec<u8> = vec![];
        match version {
            SupportedPersoTlvVersion::V0 => {
                let cert_header = PersoTlvTypesV0::make_cert_header(cert.len(), cert_name)?;
                let obj_header = PersoTlvTypesV0::make_obj_header(
                    PersoTlvTypesV0::get_crth_size(cert_header),
                    cert_type.into(),
                )?;
                data.extend(&obj_header.to_be_bytes());
                data.extend(&cert_header.to_be_bytes());
            }
            SupportedPersoTlvVersion::V1 => {
                let ver_header = PersoTlvTypesV0::make_obj_header(
                    std::mem::size_of::<PersoBlobVersionObj>(),
                    ObjType::PersoBlobVersion,
                )?;
                data.extend(&ver_header.to_be_bytes());
                data.extend(&1u16.to_be_bytes());

                let cert_header = PersoTlvTypesV1::make_cert_header(cert.len(), cert_name)?;
                let obj_header = PersoTlvTypesV1::make_obj_header(
                    PersoTlvTypesV1::get_crth_size(cert_header),
                    cert_type.into(),
                )?;
                data.extend(&obj_header.to_be_bytes());
                data.extend(&cert_header.to_be_bytes());
            }
        }
        data.extend(cert_name.as_bytes());
        data.extend(cert);
        self.data.try_extend_from_slice(&data)?;
        self.num_objs += 1;

        Ok(())
    }
}

impl From<PersoBlobBuilder> for PersoBlob {
    fn from(builder: PersoBlobBuilder) -> PersoBlob {
        PersoBlob {
            num_objs: builder.num_objs,
            next_free: builder.data.len(),
            body: builder.data,
        }
    }
}

pub struct PersoBlobParser {
    perso_blob: PersoBlob,
}

impl PersoBlobParser {
    pub fn new(perso_blob: PersoBlob) -> Self {
        Self { perso_blob }
    }

    pub fn get_obj_version(data: &[u8]) -> Result<SupportedPersoTlvVersion> {
        if let Ok(ver_obj_header) = PersoTlvTypesV0::get_obj_header(data) {
            if ver_obj_header.obj_type == ObjType::PersoBlobVersion {
                let expected_size = std::mem::size_of::<
                    <PersoTlvTypesV0 as PersoTlvTypes>::ObjHeaderType,
                >() + std::mem::size_of::<PersoBlobVersionObj>();
                if ver_obj_header.obj_size != expected_size {
                    bail!(
                        "Invalid version object size {}, expected {}",
                        ver_obj_header.obj_size,
                        expected_size
                    );
                }
                let header_len =
                    std::mem::size_of::<<PersoTlvTypesV0 as PersoTlvTypes>::ObjHeaderType>();
                let ver = u16::from_be_bytes(data[header_len..][..2].try_into()?);
                if ver != 1 {
                    bail!("Unsupported version object: {ver}");
                }
                return Ok(SupportedPersoTlvVersion::V1);
            }
        }
        Ok(SupportedPersoTlvVersion::V0)
    }

    pub fn get_obj_header(data: &[u8]) -> Result<ObjHeader> {
        let version = Self::get_obj_version(data)?;
        match version {
            SupportedPersoTlvVersion::V0 => PersoTlvTypesV0::get_obj_header(data),
            SupportedPersoTlvVersion::V1 => PersoTlvTypesV1::get_obj_header(data),
        }
    }

    pub fn get_cert<'a>(obj: &PersoBlobObject<'a>) -> Result<CertWithHeader<'a>> {
        match obj.obj_header.version {
            SupportedPersoTlvVersion::V0 => PersoTlvTypesV0::get_cert(obj.data),
            SupportedPersoTlvVersion::V1 => PersoTlvTypesV1::get_cert(obj.data),
        }
    }

    pub fn iter(&self) -> PersoBlobIterator<'_> {
        PersoBlobIterator::new(self, 0, 0)
    }
}

pub struct PersoBlobObject<'a> {
    pub obj_header: ObjHeader,
    pub data: &'a [u8],
}

impl<'a> PersoBlobObject<'a> {
    pub fn get_cert(&self) -> Result<CertWithHeader<'a>> {
        PersoBlobParser::get_cert(self)
    }
}

pub struct PersoBlobIterator<'a> {
    parser: &'a PersoBlobParser,
    current_offset: usize,
    current_obj_idx: usize,
}

impl<'a> PersoBlobIterator<'a> {
    pub fn new(parser: &'a PersoBlobParser, start_obj_idx: usize, start_offset: usize) -> Self {
        Self {
            parser,
            current_obj_idx: start_obj_idx,
            current_offset: start_offset,
        }
    }
}

impl<'a> Iterator for PersoBlobIterator<'a> {
    type Item = Result<PersoBlobObject<'a>>;

    fn next(&mut self) -> Option<Self::Item> {
        if self.current_obj_idx >= self.parser.perso_blob.num_objs {
            return None;
        }

        let remaining_data = match self.parser.perso_blob.body.get(self.current_offset..) {
            Some(data) => data,
            None => {
                return Some(Err(anyhow::anyhow!(
                    "Offset {} exceeds available data size {}",
                    self.current_offset,
                    self.parser.perso_blob.body.len()
                )));
            }
        };
        let obj_header = match PersoBlobParser::get_obj_header(remaining_data) {
            Ok(hdr) => hdr,
            Err(e) => return Some(Err(e)),
        };

        if obj_header.obj_size > remaining_data.len() {
            return Some(Err(anyhow::anyhow!(
                "Size of object {} exceeds bounds for Perso blob {}",
                obj_header.obj_size,
                remaining_data.len()
            )));
        }

        self.current_offset += obj_header.obj_size;
        self.current_obj_idx += 1;

        Some(Ok(PersoBlobObject {
            obj_header,
            data: &remaining_data[obj_header.header_size..]
                [..obj_header.obj_size - obj_header.header_size],
        }))
    }
}

trait FromBigEndianBytes {
    fn from_be_bytes(bytes: &[u8]) -> Result<Self>
    where
        Self: std::marker::Sized;
}

impl FromBigEndianBytes for u16 {
    fn from_be_bytes(bytes: &[u8]) -> Result<Self> {
        Ok(Self::from_be_bytes(bytes[..2].try_into()?))
    }
}
impl FromBigEndianBytes for u32 {
    fn from_be_bytes(bytes: &[u8]) -> Result<Self> {
        Ok(Self::from_be_bytes(bytes[..4].try_into()?))
    }
}

trait PersoTlvTypes {
    type ObjHeaderType: TryFrom<u32> + Into<u32> + FromBigEndianBytes + Copy;
    type CertHeaderType: TryFrom<u32> + Into<u32> + FromBigEndianBytes + Copy;

    const PREFIX_BYTES: usize;
    const VERSION: SupportedPersoTlvVersion;

    const OBJH_SIZE_FIELD_MASK: u32;
    const OBJH_SIZE_FIELD_SHIFT: u32;
    const OBJH_TYPE_FIELD_MASK: u32;
    const OBJH_TYPE_FIELD_SHIFT: u32;

    const CRTH_SIZE_FIELD_MASK: u32;
    const CRTH_SIZE_FIELD_SHIFT: u32;
    const CRTH_NAME_SIZE_FIELD_MASK: u32;
    const CRTH_NAME_SIZE_FIELD_SHIFT: u32;

    const MAX_CERT_NAME_LEN: usize;
    const MAX_CERT_LEN: usize;

    // Expects that `val` is Host-Endian
    fn get_obj_size(val: Self::ObjHeaderType) -> usize {
        usize::try_from((val.into() >> Self::OBJH_SIZE_FIELD_SHIFT) & Self::OBJH_SIZE_FIELD_MASK)
            .expect("ObjhSize must fit in usize")
    }

    // Expects that `val` is Host-Endian
    fn get_obj_type_raw_value(val: Self::ObjHeaderType) -> usize {
        usize::try_from((val.into() >> Self::OBJH_TYPE_FIELD_SHIFT) & Self::OBJH_TYPE_FIELD_MASK)
            .expect("ObjhType must fit in usize")
    }

    // Expects that `val` is Host-Endian
    fn get_crth_size(val: Self::CertHeaderType) -> usize {
        usize::try_from((val.into() >> Self::CRTH_SIZE_FIELD_SHIFT) & Self::CRTH_SIZE_FIELD_MASK)
            .expect("CrthSize must fit in usize")
    }

    // Expects that `val` is Host-Endian
    fn get_crth_name_size(val: Self::CertHeaderType) -> usize {
        usize::try_from(
            (val.into() >> Self::CRTH_NAME_SIZE_FIELD_SHIFT) & Self::CRTH_NAME_SIZE_FIELD_MASK,
        )
        .expect("CrthNameSize must fit in usize")
    }

    // Extract LTV object header from the input buffer.
    fn get_obj_header(data: &[u8]) -> Result<ObjHeader> {
        let header_len = Self::PREFIX_BYTES + std::mem::size_of::<Self::ObjHeaderType>();

        if data.len() < header_len {
            bail!(
                "Insufficient amount of data ({} bytes) for object header. Needs {} bytes",
                data.len(),
                header_len
            )
        }

        let obj_header = Self::ObjHeaderType::from_be_bytes(&data[Self::PREFIX_BYTES..])?;
        let inner_obj_size = Self::get_obj_size(obj_header);
        let obj_size = Self::PREFIX_BYTES + inner_obj_size;
        let obj_type = Self::get_obj_type_raw_value(obj_header);

        if obj_size > data.len() {
            bail!(
                "Object {} length {} exceeds buffer size {}",
                obj_type,
                obj_size,
                data.len()
            );
        }

        if inner_obj_size < std::mem::size_of::<Self::ObjHeaderType>() {
            bail!(
                "Object {} length {} is less than Object header length {}",
                obj_type,
                inner_obj_size,
                std::mem::size_of::<Self::ObjHeaderType>()
            );
        }

        let obj_type = obj_type.try_into()?;
        Ok(ObjHeader {
            obj_type,
            obj_size,
            header_size: header_len,
            version: Self::VERSION,
        })
    }

    // Extract certificate payload header from the input buffer.
    fn get_cert(data: &[u8]) -> Result<CertWithHeader> {
        let header_len = std::mem::size_of::<Self::CertHeaderType>();

        if header_len > data.len() {
            bail!(
                "Insufficient amount of data ({} bytes) for cert header. Needs {} bytes",
                data.len(),
                header_len
            );
        }

        let cert_header = Self::CertHeaderType::from_be_bytes(data)?;
        let wrapped_size = Self::get_crth_size(cert_header);
        if wrapped_size > data.len() {
            bail!(
                "Cert object size {} exceeds buffer size {}",
                wrapped_size,
                data.len()
            );
        }

        let cert_name_size = Self::get_crth_name_size(cert_header);
        let header_and_name_size = header_len + cert_name_size;
        if header_and_name_size > wrapped_size {
            bail!(
                "Header length {} + Cert name size {} exceeds wrapped cert size {}",
                header_len,
                cert_name_size,
                wrapped_size
            )
        }
        let cert_name = std::str::from_utf8(&data[header_len..header_len + cert_name_size])?;
        log::info!("processing cert {cert_name}");

        let cert_body: Vec<u8> = data[header_and_name_size..wrapped_size].to_vec();

        Ok(CertWithHeader {
            wrapped_size,
            cert_name,
            cert_body,
        })
    }

    // Helper functions used to pack LTV object and Certificate payload headers.
    // `object_size` is the size of the object only, excluding the header
    fn make_obj_header(object_size: usize, otype: ObjType) -> Result<Self::ObjHeaderType> {
        let size = u32::try_from(
            object_size
                .checked_add(std::mem::size_of::<Self::ObjHeaderType>())
                .ok_or(anyhow::anyhow!("Integer addition overflow"))?,
        )?;
        let otype = u32::try_from(otype)?;
        if size > Self::OBJH_SIZE_FIELD_MASK {
            bail!("Can't create object of size {size}")
        }

        let obj_size_val = (size & Self::OBJH_SIZE_FIELD_MASK) << Self::OBJH_SIZE_FIELD_SHIFT;
        let obj_type_val = (otype & Self::OBJH_TYPE_FIELD_MASK) << Self::OBJH_TYPE_FIELD_SHIFT;
        let obj_header_val = obj_size_val | obj_type_val;

        Self::ObjHeaderType::try_from(obj_header_val)
            .map_err(|_| anyhow::anyhow!("Failed to create ObjHeader from {obj_header_val}"))
    }

    // `cert_body_size` is size of the cert body only, exclusing the name and cert header
    fn make_cert_header(cert_body_size: usize, cert_name: &str) -> Result<Self::CertHeaderType> {
        let cert_body_size = u32::try_from(cert_body_size)?;
        let name_len = u32::try_from(cert_name.len())?;

        if name_len > Self::CRTH_NAME_SIZE_FIELD_MASK {
            bail!(
                "Can't create certificate wrapper for name \"{}\"",
                cert_name
            )
        }

        let wrapped_size =
            cert_body_size + name_len + u32::try_from(std::mem::size_of::<Self::CertHeaderType>())?;
        if wrapped_size > Self::CRTH_SIZE_FIELD_MASK {
            bail!("Can't create a certificate wrapper of size {wrapped_size}")
        }

        let cert_size_val =
            (wrapped_size & Self::CRTH_SIZE_FIELD_MASK) << Self::CRTH_SIZE_FIELD_SHIFT;
        let cert_name_size_val =
            (name_len & Self::CRTH_NAME_SIZE_FIELD_MASK) << Self::CRTH_NAME_SIZE_FIELD_SHIFT;
        let cert_header_val = cert_size_val | cert_name_size_val;

        Self::CertHeaderType::try_from(cert_header_val)
            .map_err(|_| anyhow::anyhow!("Failed to create CertHeader from {cert_header_val}"))
    }
}

struct PersoTlvTypesV0;
struct PersoTlvTypesV1;

impl PersoTlvTypes for PersoTlvTypesV0 {
    type ObjHeaderType = perso_tlv_objects::perso_tlv_object_header_t;
    type CertHeaderType = perso_tlv_objects::perso_tlv_cert_header_t;

    const PREFIX_BYTES: usize = 0;
    const VERSION: SupportedPersoTlvVersion = SupportedPersoTlvVersion::V0;

    const OBJH_SIZE_FIELD_MASK: u32 =
        perso_tlv_objects::perso_tlv_obj_header_fields_v0_kObjhSizeFieldMaskV0;
    const OBJH_SIZE_FIELD_SHIFT: u32 =
        perso_tlv_objects::perso_tlv_obj_header_fields_v0_kObjhSizeFieldShiftV0;
    const OBJH_TYPE_FIELD_MASK: u32 =
        perso_tlv_objects::perso_tlv_obj_header_fields_v0_kObjhTypeFieldMaskV0;
    const OBJH_TYPE_FIELD_SHIFT: u32 =
        perso_tlv_objects::perso_tlv_obj_header_fields_v0_kObjhTypeFieldShiftV0;

    const CRTH_SIZE_FIELD_MASK: u32 =
        perso_tlv_objects::perso_tlv_cert_header_fields_v0_kCrthSizeFieldMaskV0;
    const CRTH_SIZE_FIELD_SHIFT: u32 =
        perso_tlv_objects::perso_tlv_cert_header_fields_v0_kCrthSizeFieldShiftV0;
    const CRTH_NAME_SIZE_FIELD_MASK: u32 =
        perso_tlv_objects::perso_tlv_cert_header_fields_v0_kCrthNameSizeFieldMaskV0;
    const CRTH_NAME_SIZE_FIELD_SHIFT: u32 =
        perso_tlv_objects::perso_tlv_cert_header_fields_v0_kCrthNameSizeFieldShiftV0;

    const MAX_CERT_NAME_LEN: usize =
        perso_tlv_objects::perso_tlv_cert_header_fields_v0_kCrthNameSizeFieldMaskV0 as usize;
    const MAX_CERT_LEN: usize =
        (perso_tlv_objects::perso_tlv_obj_header_fields_v0_kObjhSizeFieldMaskV0 as usize)
            - std::mem::size_of::<Self::ObjHeaderType>()
            - std::mem::size_of::<Self::CertHeaderType>()
            - Self::MAX_CERT_NAME_LEN;
}

impl PersoTlvTypes for PersoTlvTypesV1 {
    type ObjHeaderType = perso_tlv_objects::perso_tlv_object_header_v1_t;
    type CertHeaderType = perso_tlv_objects::perso_tlv_cert_header_v1_t;

    const PREFIX_BYTES: usize = std::mem::size_of::<
        <PersoTlvTypesV0 as PersoTlvTypes>::ObjHeaderType,
    >() + std::mem::size_of::<PersoBlobVersionObj>();
    const VERSION: SupportedPersoTlvVersion = SupportedPersoTlvVersion::V1;

    const OBJH_SIZE_FIELD_MASK: u32 =
        perso_tlv_objects::perso_tlv_obj_header_fields_v1_kObjhSizeFieldMaskV1;
    const OBJH_SIZE_FIELD_SHIFT: u32 =
        perso_tlv_objects::perso_tlv_obj_header_fields_v1_kObjhSizeFieldShiftV1;
    const OBJH_TYPE_FIELD_MASK: u32 =
        perso_tlv_objects::perso_tlv_obj_header_fields_v1_kObjhTypeFieldMaskV1;
    const OBJH_TYPE_FIELD_SHIFT: u32 =
        perso_tlv_objects::perso_tlv_obj_header_fields_v1_kObjhTypeFieldShiftV1;

    const CRTH_SIZE_FIELD_MASK: u32 =
        perso_tlv_objects::perso_tlv_cert_header_fields_v1_kCrthSizeFieldMaskV1;
    const CRTH_SIZE_FIELD_SHIFT: u32 =
        perso_tlv_objects::perso_tlv_cert_header_fields_v1_kCrthSizeFieldShiftV1;
    const CRTH_NAME_SIZE_FIELD_MASK: u32 =
        perso_tlv_objects::perso_tlv_cert_header_fields_v1_kCrthNameSizeFieldMaskV1;
    const CRTH_NAME_SIZE_FIELD_SHIFT: u32 =
        perso_tlv_objects::perso_tlv_cert_header_fields_v1_kCrthNameSizeFieldShiftV1;

    const MAX_CERT_NAME_LEN: usize =
        perso_tlv_objects::perso_tlv_cert_header_fields_v1_kCrthNameSizeFieldMaskV1 as usize;
    const MAX_CERT_LEN: usize =
        (perso_tlv_objects::perso_tlv_obj_header_fields_v1_kObjhSizeFieldMaskV1 as usize)
            - std::mem::size_of::<Self::ObjHeaderType>()
            - std::mem::size_of::<Self::CertHeaderType>()
            - Self::MAX_CERT_NAME_LEN;
}

#[repr(C)]
#[derive(Debug)]
struct PersoBlobVersionObj {
    version: u16,
}

const _: () = {
    assert!(
        std::mem::size_of::<perso_tlv_blob_version_payload>()
            == std::mem::size_of::<PersoBlobVersionObj>(),
        "perso_tlv_blob_version_payload should have the same size as PersoBlobVersionObj"
    );
};

#[allow(dead_code)]
impl PersoBlobVersionObj {
    pub fn new(version: u16) -> Self {
        Self { version }
    }

    pub fn read_from_perso_blob(blob: &PersoBlob) -> Result<Option<Self>> {
        if blob.num_objs == 0 {
            bail!("Cannot determine version for an empty Perso Blob")
        }
        let first_obj_header = PersoTlvTypesV0::get_obj_header(&blob.body)?;
        let first_obj_type = first_obj_header.obj_type;
        if first_obj_type == ObjType::PersoBlobVersion {
            let obj_header_size =
                std::mem::size_of::<<PersoTlvTypesV0 as PersoTlvTypes>::ObjHeaderType>();
            if first_obj_header.obj_size != (std::mem::size_of::<Self>() + obj_header_size) {
                bail!(
                    "Object size: {}. Expected size: {}",
                    first_obj_header.obj_size,
                    std::mem::size_of::<Self>() + obj_header_size
                )
            }
            let ver = u16::from_be_bytes(blob.body[obj_header_size..][..2].try_into()?);
            if ver != 1 {
                bail!("Unsupported version object: {ver}");
            }
            return Ok(Some(Self { version: ver }));
        }
        Ok(None)
    }
}

impl TryFrom<PersoBlobVersionObj> for Vec<u8> {
    type Error = anyhow::Error;

    fn try_from(obj: PersoBlobVersionObj) -> Result<Vec<u8>, Self::Error> {
        let mut data = PersoTlvTypesV0::make_obj_header(
            std::mem::size_of::<PersoBlobVersionObj>(),
            ObjType::PersoBlobVersion,
        )?
        .to_be_bytes()
        .to_vec();
        data.extend(&obj.version.to_be_bytes());
        Ok(data)
    }
}

#[cfg(test)]
mod tests {

    mod perso_blob_version_object_tests {
        use core::convert::TryInto;

        use crate::PersoBlobVersionObj;
        use arrayvec::ArrayVec;
        use ujson_lib::provisioning_data::PersoBlob;
        #[test]
        fn perso_blob_version_object_into_bytes() {
            let bytes: Vec<u8> = PersoBlobVersionObj::new(0).try_into().unwrap();
            assert_eq!(bytes, vec![0xF0, 0x04, 0x00, 0x00]);

            let bytes: Vec<u8> = PersoBlobVersionObj::new(1).try_into().unwrap();
            assert_eq!(bytes, vec![0xF0, 0x04, 0x00, 0x01]);
        }

        #[test]
        fn perso_blob_version_object_from_valid_perso_blob() {
            let dev_seed_bytes_v0 = [0x20, 0x08, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06];
            let perso_blob = PersoBlob {
                num_objs: 1,
                next_free: dev_seed_bytes_v0.len(),
                body: dev_seed_bytes_v0.into_iter().collect(),
            };
            let obj = PersoBlobVersionObj::read_from_perso_blob(&perso_blob).unwrap();
            assert!(obj.is_none());

            let version_blob_v1 = [0xF0, 0x04, 0x00, 0x01];
            let perso_blob = PersoBlob {
                num_objs: 2,
                next_free: version_blob_v1.len() + dev_seed_bytes_v0.len(),
                body: version_blob_v1
                    .into_iter()
                    .chain(dev_seed_bytes_v0)
                    .collect(),
            };
            let obj = PersoBlobVersionObj::read_from_perso_blob(&perso_blob).unwrap();
            let obj = obj.unwrap();
            assert_eq!(obj.version, 1);
        }

        #[test]
        fn perso_blob_version_object_from_invalid_perso_blob() {
            let perso_blob = PersoBlob {
                num_objs: 0,
                next_free: 0,
                body: ArrayVec::new(),
            };
            assert!(PersoBlobVersionObj::read_from_perso_blob(&perso_blob).is_err());

            let invalid_obj_header = [0x20];
            let perso_blob = PersoBlob {
                num_objs: 1,
                next_free: invalid_obj_header.len(),
                body: invalid_obj_header.into_iter().collect(),
            };
            assert!(PersoBlobVersionObj::read_from_perso_blob(&perso_blob).is_err());

            let invalid_version_obj_size = [0xF0, 0x03, 0x00, 0x01];
            let perso_blob = PersoBlob {
                num_objs: 1,
                next_free: invalid_version_obj_size.len(),
                body: invalid_version_obj_size.into_iter().collect(),
            };
            assert!(PersoBlobVersionObj::read_from_perso_blob(&perso_blob).is_err());

            let invalid_version_obj = [0xF0, 0x04, 0x00];
            let perso_blob = PersoBlob {
                num_objs: 1,
                next_free: invalid_version_obj.len(),
                body: invalid_version_obj.into_iter().collect(),
            };
            assert!(PersoBlobVersionObj::read_from_perso_blob(&perso_blob).is_err());

            let disallowed_version_obj_v0 = [0xF0, 0x04, 0x00, 0x00];
            let perso_blob = PersoBlob {
                num_objs: 1,
                next_free: disallowed_version_obj_v0.len(),
                body: disallowed_version_obj_v0.into_iter().collect(),
            };
            assert!(PersoBlobVersionObj::read_from_perso_blob(&perso_blob).is_err());
        }
    }

    mod perso_tlv_types_v0_tests {
        use crate::ObjType;
        use crate::PersoTlvTypes;
        use crate::PersoTlvTypesV0;
        use crate::SupportedPersoTlvVersion;

        #[test]
        fn get_obj_size_test() {
            assert_eq!(
                PersoTlvTypesV0::get_obj_size(u16::from_be_bytes([0xf0, 0x03])),
                3
            );
            assert_eq!(
                PersoTlvTypesV0::get_obj_size(u16::from_be_bytes([0xf0, 0xab])),
                171
            );
            assert_eq!(
                PersoTlvTypesV0::get_obj_size(u16::from_be_bytes([0xff, 0xff])),
                4095
            );
        }

        #[test]
        fn get_obj_type_test() {
            assert_eq!(
                PersoTlvTypesV0::get_obj_type_raw_value(u16::from_be_bytes([0x0f, 0xff])),
                0
            );
            assert_eq!(
                PersoTlvTypesV0::get_obj_type_raw_value(u16::from_be_bytes([0xaf, 0xff])),
                10
            );
            assert_eq!(
                PersoTlvTypesV0::get_obj_type_raw_value(u16::from_be_bytes([0xff, 0xff])),
                15
            );
        }

        #[test]
        fn get_crth_size() {
            assert_eq!(
                PersoTlvTypesV0::get_crth_size(u16::from_be_bytes([0xf0, 0x03])),
                3
            );
            assert_eq!(
                PersoTlvTypesV0::get_crth_size(u16::from_be_bytes([0xf0, 0xba])),
                186
            );
            assert_eq!(
                PersoTlvTypesV0::get_crth_size(u16::from_be_bytes([0xfc, 0xba])),
                3258
            );
        }

        #[test]
        fn get_crth_name_size() {
            assert_eq!(
                PersoTlvTypesV0::get_crth_name_size(u16::from_be_bytes([0x4f, 0xff])),
                4
            );
            assert_eq!(
                PersoTlvTypesV0::get_crth_name_size(u16::from_be_bytes([0xcf, 0xff])),
                12
            );
        }

        #[test]
        fn get_obj_header_valid() {
            let hdr = PersoTlvTypesV0::get_obj_header(&[
                0x70, 0x09, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07,
            ])
            .unwrap();
            assert_eq!(hdr.obj_size, 9);
            assert_eq!(hdr.header_size, 2);
            assert_eq!(hdr.obj_type, ObjType::PersoSha256Hash);
            assert_eq!(hdr.version, SupportedPersoTlvVersion::V0);

            let hdr = PersoTlvTypesV0::get_obj_header(&[0xf0, 0x04, 0x03, 0x00]).unwrap();
            assert_eq!(hdr.obj_size, 4);
            assert_eq!(hdr.header_size, 2);
            assert_eq!(hdr.obj_type, ObjType::PersoBlobVersion);
            assert_eq!(hdr.version, SupportedPersoTlvVersion::V0);
        }

        #[test]
        fn get_obj_header_invalid_insufficient_header_len() {
            assert!(PersoTlvTypesV0::get_obj_header(&[]).is_err());
            assert!(PersoTlvTypesV0::get_obj_header(&[0x01]).is_err());
        }

        #[test]
        fn get_obj_header_invalid_obj_len() {
            assert!(PersoTlvTypesV0::get_obj_header(&[0x30, 0x09]).is_err());
            assert!(PersoTlvTypesV0::get_obj_header(&[0x30, 0x05, 0x01, 0x02]).is_err());

            assert!(PersoTlvTypesV0::get_obj_header(&[0x30, 0x00, 0x01, 0x02]).is_err());
            assert!(PersoTlvTypesV0::get_obj_header(&[0x30, 0x01, 0x01, 0x02]).is_err());
        }

        #[test]
        fn get_obj_header_invalid_obj_type() {
            assert!(PersoTlvTypesV0::get_obj_header(&[0xd0, 0x03, 0x01]).is_err());
        }

        #[test]
        fn get_cert_valid() {
            let unendorsed_cert_bytes = [0x40, 0x08, b'c', b'e', b'r', b't', 0x01, 0x02];
            let cert_obj = PersoTlvTypesV0::get_cert(&unendorsed_cert_bytes).unwrap();
            assert_eq!(cert_obj.wrapped_size, 8);
            assert_eq!(cert_obj.cert_name, "cert");
            assert_eq!(cert_obj.cert_body, vec![0x01, 0x02]);

            let endorsed_cert_bytes = [
                0x50, 0x0b, b'c', b'e', b'r', b't', b'1', 0x01, 0x02, 0x03, 0x04,
            ];
            let cert_obj = PersoTlvTypesV0::get_cert(&endorsed_cert_bytes).unwrap();
            assert_eq!(cert_obj.wrapped_size, 11);
            assert_eq!(cert_obj.cert_name, "cert1");
            assert_eq!(cert_obj.cert_body, vec![0x01, 0x02, 0x03, 0x04]);
        }

        #[test]
        fn get_cert_insufficient_header_len() {
            assert!(PersoTlvTypesV0::get_cert(&[]).is_err());
            assert!(PersoTlvTypesV0::get_cert(&[0x05]).is_err());
        }

        #[test]
        fn get_cert_insufficient_wrapped_data() {
            assert!(PersoTlvTypesV0::get_cert(&[0x40, 0x08]).is_err());
            assert!(
                PersoTlvTypesV0::get_cert(&[0x40, 0x08, b'c', b'e', b'r', b't', 0x01]).is_err()
            );
        }

        #[test]
        fn get_cert_invalid_name_size() {
            assert!(
                PersoTlvTypesV0::get_cert(&[0xF0, 0x08, b'c', b'e', b'r', b't', 0x01, 0x02])
                    .is_err()
            );
        }

        #[test]
        fn get_cert_invalid_utf8_name() {
            assert!(
                PersoTlvTypesV0::get_cert(&[
                    0x40, 0x08, 0xf5, 0x80, 0x80, 0x80, 0x01, 0x02, 0x03, 0x04
                ])
                .is_err()
            );
        }

        #[test]
        fn make_obj_header_valid() {
            let hdr = PersoTlvTypesV0::make_obj_header(20, ObjType::WasTbsHmac).unwrap();
            assert_eq!(hdr.to_be_bytes(), [0x40, 0x16]);

            let hdr = PersoTlvTypesV0::make_obj_header(32, ObjType::PersoSha256Hash).unwrap();
            assert_eq!(hdr.to_be_bytes(), [0x70, 0x22]);
        }

        #[test]
        fn make_obj_header_invalid_size_too_large() {
            assert!(PersoTlvTypesV0::make_obj_header(4094, ObjType::WasTbsHmac).is_err());
            assert!(PersoTlvTypesV0::make_obj_header(6000, ObjType::WasTbsHmac).is_err());
        }

        #[test]
        fn make_cert_header_valid() {
            let hdr = PersoTlvTypesV0::make_cert_header(128, "cert").unwrap();
            assert_eq!(hdr.to_be_bytes(), [0x40, 0x86]);
        }

        #[test]
        fn make_cert_header_invalid_cert_name_too_large() {
            assert!(PersoTlvTypesV0::make_cert_header(128, "certificate_name_too_large").is_err());
        }

        #[test]
        fn make_cert_header_invalid_wrapped_cert_size_too_large() {
            assert!(PersoTlvTypesV0::make_cert_header(4090, "cert").is_err());
            assert!(PersoTlvTypesV0::make_cert_header(6000, "cert").is_err());
        }
    }

    mod perso_tlv_types_v1_tests {
        use crate::ObjType;
        use crate::PersoTlvTypes;
        use crate::PersoTlvTypesV1;
        use crate::SupportedPersoTlvVersion;

        #[test]
        fn get_obj_size_test() {
            assert_eq!(
                PersoTlvTypesV1::get_obj_size(u32::from_be_bytes([0xff, 0x00, 0x00, 0x03])),
                3
            );
            assert_eq!(
                PersoTlvTypesV1::get_obj_size(u32::from_be_bytes([0xff, 0x00, 0xab, 0xcd])),
                43981
            );
            assert_eq!(
                PersoTlvTypesV1::get_obj_size(u32::from_be_bytes([0xff, 0xab, 0xcd, 0xef])),
                11259375
            );
        }

        #[test]
        fn get_obj_type_test() {
            assert_eq!(
                PersoTlvTypesV1::get_obj_type_raw_value(u32::from_be_bytes([
                    0x02, 0xff, 0xff, 0xff
                ])),
                2
            );
            assert_eq!(
                PersoTlvTypesV1::get_obj_type_raw_value(u32::from_be_bytes([
                    0xab, 0xff, 0xff, 0xff
                ])),
                171
            );
            assert_eq!(
                PersoTlvTypesV1::get_obj_type_raw_value(u32::from_be_bytes([
                    0xff, 0xff, 0xff, 0xff
                ])),
                255
            );
        }

        #[test]
        fn get_crth_size() {
            assert_eq!(
                PersoTlvTypesV1::get_crth_size(u32::from_be_bytes([0xff, 0x00, 0x00, 0x05])),
                5
            );
            assert_eq!(
                PersoTlvTypesV1::get_crth_size(u32::from_be_bytes([0xff, 0x00, 0x00, 0xba])),
                186
            );
            assert_eq!(
                PersoTlvTypesV1::get_crth_size(u32::from_be_bytes([0xff, 0x00, 0xdc, 0xba])),
                56506
            );
            assert_eq!(
                PersoTlvTypesV1::get_crth_size(u32::from_be_bytes([0xff, 0xfe, 0xdc, 0xba])),
                16702650
            );
        }

        #[test]
        fn get_crth_name_size() {
            assert_eq!(
                PersoTlvTypesV1::get_crth_name_size(u32::from_be_bytes([0x04, 0xff, 0xff, 0xff])),
                4
            );
            assert_eq!(
                PersoTlvTypesV1::get_crth_name_size(u32::from_be_bytes([0xab, 0xff, 0xff, 0xff])),
                171
            );
            assert_eq!(
                PersoTlvTypesV1::get_crth_name_size(u32::from_be_bytes([0xff, 0xff, 0xff, 0xff])),
                255
            );
        }

        #[test]
        fn get_obj_header_valid() {
            let hdr = PersoTlvTypesV1::get_obj_header(&[
                0xf0, 0x04, 0x00, 0x01, 0x07, 0x00, 0x00, 0x09, 0x01, 0x02, 0x03, 0x04, 0x05,
            ])
            .unwrap();
            assert_eq!(hdr.obj_size, 13);
            assert_eq!(hdr.header_size, 8);
            assert_eq!(hdr.obj_type, ObjType::PersoSha256Hash);
            assert_eq!(hdr.version, SupportedPersoTlvVersion::V1);
        }

        #[test]
        fn get_obj_header_invalid_insufficient_header_len() {
            assert!(PersoTlvTypesV1::get_obj_header(&[]).is_err());
            assert!(PersoTlvTypesV1::get_obj_header(&[0x01]).is_err());
            assert!(PersoTlvTypesV1::get_obj_header(&[0x01, 0x02]).is_err());
            assert!(PersoTlvTypesV1::get_obj_header(&[0x01, 0x02, 0x03]).is_err());
            assert!(PersoTlvTypesV1::get_obj_header(&[0xf0, 0x04, 0x00, 0x01]).is_err());
            assert!(
                PersoTlvTypesV1::get_obj_header(&[0xf0, 0x04, 0x00, 0x01, 0x07, 0x00, 0x00])
                    .is_err()
            );
        }

        #[test]
        fn get_obj_header_invalid_obj_len() {
            assert!(
                PersoTlvTypesV1::get_obj_header(&[0xf0, 0x04, 0x00, 0x01, 0x03, 0x00, 0x00, 0x09])
                    .is_err()
            );
            assert!(
                PersoTlvTypesV1::get_obj_header(&[
                    0xf0, 0x04, 0x00, 0x01, 0x03, 0x00, 0x00, 0x08, 0x01, 0x02
                ])
                .is_err()
            );

            assert!(
                PersoTlvTypesV1::get_obj_header(&[
                    0xf0, 0x04, 0x00, 0x01, 0x03, 0x00, 0x00, 0x00, 0x01, 0x02
                ])
                .is_err()
            );
            assert!(
                PersoTlvTypesV1::get_obj_header(&[
                    0xf0, 0x04, 0x00, 0x01, 0x03, 0x00, 0x00, 0x01, 0x01, 0x02
                ])
                .is_err()
            );
            assert!(
                PersoTlvTypesV1::get_obj_header(&[
                    0xf0, 0x04, 0x00, 0x01, 0x03, 0x00, 0x00, 0x02, 0x01, 0x02
                ])
                .is_err()
            );
            assert!(
                PersoTlvTypesV1::get_obj_header(&[
                    0xf0, 0x04, 0x00, 0x01, 0x03, 0x00, 0x00, 0x03, 0x01, 0x02
                ])
                .is_err()
            );
        }

        #[test]
        fn get_obj_header_invalid_obj_type() {
            assert!(
                PersoTlvTypesV1::get_obj_header(&[
                    0xf0, 0x04, 0x00, 0x01, 0xd0, 0x00, 0x00, 0x05, 0x01
                ])
                .is_err()
            );
        }

        #[test]
        fn get_cert_valid() {
            let unendorsed_cert_bytes =
                [0x04, 0x00, 0x00, 0x0a, b'c', b'e', b'r', b't', 0x01, 0x02];
            let cert_obj = PersoTlvTypesV1::get_cert(&unendorsed_cert_bytes).unwrap();
            assert_eq!(cert_obj.wrapped_size, 10);
            assert_eq!(cert_obj.cert_name, "cert");
            assert_eq!(cert_obj.cert_body, vec![0x01, 0x02]);

            let endorsed_cert_bytes = [
                0x05, 0x00, 0x00, 0x0d, b'c', b'e', b'r', b't', b'1', 0x01, 0x02, 0x03, 0x04,
            ];
            let cert_obj = PersoTlvTypesV1::get_cert(&endorsed_cert_bytes).unwrap();
            assert_eq!(cert_obj.wrapped_size, 13);
            assert_eq!(cert_obj.cert_name, "cert1");
            assert_eq!(cert_obj.cert_body, vec![0x01, 0x02, 0x03, 0x04]);
        }

        #[test]
        fn get_cert_insufficient_header_len() {
            assert!(PersoTlvTypesV1::get_cert(&[]).is_err());
            assert!(PersoTlvTypesV1::get_cert(&[0x05]).is_err());
            assert!(PersoTlvTypesV1::get_cert(&[0x05, 0x06]).is_err());
            assert!(PersoTlvTypesV1::get_cert(&[0x05, 0x06, 0x07]).is_err());
        }

        #[test]
        fn get_cert_insufficient_wrapped_data() {
            assert!(PersoTlvTypesV1::get_cert(&[0x04, 0x00, 0x00, 0x08]).is_err());
            assert!(
                PersoTlvTypesV1::get_cert(&[0x04, 0x00, 0x00, 0x0a, b'c', b'e', b'r', b't', 0x01])
                    .is_err()
            );
        }

        #[test]
        fn get_cert_invalid_name_size() {
            assert!(
                PersoTlvTypesV1::get_cert(&[
                    0x0F, 0x00, 0x00, 0x0a, b'c', b'e', b'r', b't', 0x01, 0x02
                ])
                .is_err()
            );
        }

        #[test]
        fn get_cert_invalid_utf8_name() {
            assert!(
                PersoTlvTypesV1::get_cert(&[
                    0x04, 0x00, 0x00, 0x0c, 0xf5, 0x80, 0x80, 0x80, 0x01, 0x02, 0x03, 0x04
                ])
                .is_err()
            );
        }

        #[test]
        fn make_obj_header_valid() {
            let hdr = PersoTlvTypesV1::make_obj_header(20, ObjType::WasTbsHmac).unwrap();
            assert_eq!(hdr.to_be_bytes(), [0x04, 0x00, 0x00, 0x18]);

            let hdr = PersoTlvTypesV1::make_obj_header(32, ObjType::PersoSha256Hash).unwrap();
            assert_eq!(hdr.to_be_bytes(), [0x07, 0x00, 0x00, 0x24]);

            let hdr = PersoTlvTypesV1::make_obj_header(8192, ObjType::UnendorsedX509Cert).unwrap();
            assert_eq!(hdr.to_be_bytes(), [0x00, 0x00, 0x20, 0x04]);
        }

        #[test]
        fn make_obj_header_invalid_size_too_large() {
            assert!(PersoTlvTypesV1::make_obj_header(16777216, ObjType::WasTbsHmac).is_err());
            assert!(PersoTlvTypesV1::make_obj_header(60000000, ObjType::WasTbsHmac).is_err());
        }

        #[test]
        fn make_cert_header_valid() {
            let hdr = PersoTlvTypesV1::make_cert_header(128, "cert").unwrap();
            assert_eq!(hdr.to_be_bytes(), [0x04, 0x00, 0x00, 0x88]);

            let hdr =
                PersoTlvTypesV1::make_cert_header(16384, "certificate_with_somewhat_longer_name")
                    .unwrap();
            assert_eq!(hdr.to_be_bytes(), [0x25, 0x00, 0x40, 0x29]);
        }

        #[test]
        fn make_cert_header_invalid_cert_name_too_large() {
            let cert_name = vec![b'a'; 256];
            let cert_name = String::from_utf8(cert_name).unwrap();
            assert!(PersoTlvTypesV1::make_cert_header(128, &cert_name).is_err());
        }

        #[test]
        fn make_cert_header_invalid_wrapped_cert_size_too_large() {
            assert!(PersoTlvTypesV1::make_cert_header(16777208, "cert").is_err());
            assert!(PersoTlvTypesV1::make_cert_header(60000000, "cert").is_err());
        }
    }

    mod perso_blob_builder_tests {
        use crate::EndorsedCertType;
        use crate::PersoBlobBuilder;
        use ujson_lib::provisioning_data::PersoBlob;

        #[test]
        fn perso_blob_no_data() {
            let perso_blob_builder = PersoBlobBuilder::new();
            let perso_blob: PersoBlob = perso_blob_builder.into();
            assert_eq!(perso_blob.num_objs, 0);
            assert_eq!(perso_blob.body.len(), 0);
            assert_eq!(perso_blob.next_free, 0);
        }

        #[test]
        fn perso_blob_single_v0_cert() {
            let mut perso_blob_builder = PersoBlobBuilder::new();
            perso_blob_builder
                .push_endorsed_cert(
                    "cert",
                    &vec![0x01, 0x02, 0x03, 0x04, 0x05],
                    EndorsedCertType::EndorsedX509Cert,
                )
                .unwrap();
            let perso_blob: PersoBlob = perso_blob_builder.into();
            assert_eq!(perso_blob.num_objs, 1);
            assert_eq!(
                perso_blob.body.as_slice(),
                &[
                    0x10, 0x0d, 0x40, 0x0b, b'c', b'e', b'r', b't', 0x01, 0x02, 0x03, 0x04, 0x05
                ]
            );
            assert_eq!(perso_blob.next_free, 13);
        }

        #[test]
        fn perso_blob_two_v0_certs() {
            let mut perso_blob_builder = PersoBlobBuilder::new();
            perso_blob_builder
                .push_endorsed_cert(
                    "cert",
                    &vec![0x01, 0x02, 0x03, 0x04, 0x05],
                    EndorsedCertType::EndorsedX509Cert,
                )
                .unwrap();
            perso_blob_builder
                .push_endorsed_cert(
                    "cert2",
                    &vec![0x06, 0x07, 0x08, 0x09, 0x0a, 0x0b, 0x0c],
                    EndorsedCertType::EndorsedX509Cert,
                )
                .unwrap();
            let perso_blob: PersoBlob = perso_blob_builder.into();
            let expected_perso_body_bytes = [
                // Cert 1
                0x10, 0x0d, 0x40, 0x0b, b'c', b'e', b'r', b't', 0x01, 0x02, 0x03, 0x04, 0x05,
                // Cert 2
                0x10, 0x10, 0x50, 0x0e, b'c', b'e', b'r', b't', b'2', 0x06, 0x07, 0x08, 0x09, 0x0a,
                0x0b, 0x0c,
            ];
            assert_eq!(perso_blob.num_objs, 2);
            assert_eq!(perso_blob.body.as_slice(), &expected_perso_body_bytes);
            assert_eq!(perso_blob.next_free, 29);
        }

        #[test]
        fn perso_blob_oversized_name_v1_cert() {
            let mut perso_blob_builder = PersoBlobBuilder::new();
            // Name with 16 characters (exceeds V0 limit of 15 chars)
            let long_cert_name = "0123456789abcdef";
            perso_blob_builder
                .push_endorsed_cert(
                    long_cert_name,
                    &vec![0x01, 0x02, 0x03, 0x04, 0x05],
                    EndorsedCertType::EndorsedX509Cert,
                )
                .unwrap();
            let perso_blob: PersoBlob = perso_blob_builder.into();

            #[rustfmt::skip]
            let expected_perso_body_bytes = [
                // Version prefix
                0xf0, 0x04, 0x00, 0x01,
                // Cert 1 (V1 header)
                0x01, 0x00, 0x00, 0x1d, 0x10, 0x00, 0x00, 0x19,
                b'0', b'1', b'2', b'3', b'4', b'5', b'6', b'7', b'8', b'9', b'a', b'b', b'c', b'd', b'e', b'f',
                0x01, 0x02, 0x03, 0x04, 0x05,
            ];
            assert_eq!(perso_blob.num_objs, 1);
            assert_eq!(perso_blob.body.as_slice(), &expected_perso_body_bytes);
        }

        #[test]
        fn perso_blob_oversized_body_v1_cert() {
            let mut perso_blob_builder = PersoBlobBuilder::new();
            // Body with 4090 bytes (v0_crth_size = 2 + 4 + 4090 = 4096 > 4095)
            let large_cert_body = vec![0x01; 4090];
            perso_blob_builder
                .push_endorsed_cert("cert", &large_cert_body, EndorsedCertType::EndorsedX509Cert)
                .unwrap();
            let perso_blob: PersoBlob = perso_blob_builder.into();
            assert_eq!(perso_blob.num_objs, 1);
            // Verify it has the V1 version prefix
            assert_eq!(&perso_blob.body[0..4], &[0xf0, 0x04, 0x00, 0x01]);
        }

        #[test]
        fn perso_blob_run_out_of_space() {
            let large_cert_body = vec![0x01; 8192];
            let mut perso_blob_builder = PersoBlobBuilder::new();
            perso_blob_builder
                .push_endorsed_cert(
                    "large_cert",
                    &large_cert_body,
                    EndorsedCertType::EndorsedX509Cert,
                )
                .unwrap();

            // Adding a 2nd large cert will cause Perso blob to run out of space
            let large_cert_body = vec![0x02; 5076];
            assert!(
                perso_blob_builder
                    .push_endorsed_cert(
                        "large_cert2",
                        &large_cert_body,
                        EndorsedCertType::EndorsedX509Cert
                    )
                    .is_err()
            );
        }
    }

    mod perso_blob_parser_tests {
        use crate::PersoBlobParser;

        fn get_v0_cert_bytes() -> Vec<u8> {
            vec![0x00, 0x0a, 0x40, 0x08, b'c', b'e', b'r', b't', 0x01, 0x02]
        }

        fn get_v1_cert_bytes() -> Vec<u8> {
            vec![
                0xf0, 0x04, 0x00, 0x01, 0x00, 0x00, 0x00, 0x0e, 0x04, 0x00, 0x00, 0x0a, b'c', b'e',
                b'r', b't', 0x01, 0x02,
            ]
        }

        #[test]
        fn get_obj_header_v0() {
            let perso_body_bytes = get_v0_cert_bytes();
            let obj_hdr = PersoBlobParser::get_obj_header(&perso_body_bytes).unwrap();
            assert_eq!(obj_hdr.obj_size, 10);
            assert_eq!(obj_hdr.header_size, 2);
            assert_eq!(obj_hdr.version, crate::SupportedPersoTlvVersion::V0);
        }

        #[test]
        fn get_obj_header_v1() {
            let perso_body_bytes = get_v1_cert_bytes();
            let obj_hdr = PersoBlobParser::get_obj_header(&perso_body_bytes).unwrap();
            assert_eq!(obj_hdr.obj_size, 18);
            assert_eq!(obj_hdr.header_size, 8);
            assert_eq!(obj_hdr.version, crate::SupportedPersoTlvVersion::V1);
        }

        #[test]
        fn get_obj_version_disallowed_v0() {
            let invalid_bytes = vec![0xf0, 0x04, 0x00, 0x00, 0x00, 0x00];
            assert!(PersoBlobParser::get_obj_version(&invalid_bytes).is_err());
        }
    }

    mod perso_blob_iterator_tests {
        use crate::ObjType;
        use crate::PersoBlobParser;
        use core::iter::{IntoIterator, Iterator};
        use ujson_lib::provisioning_data::PersoBlob;

        #[test]
        fn v0_blob_iter() {
            #[rustfmt::skip]
            let perso_blob_bytes = vec![
                // Cert 1
                0x10, 0x0d, 0x40, 0x0b, b'c', b'e', b'r', b't', 0x01, 0x02, 0x03, 0x04, 0x05,
                // Cert 2
                0x10, 0x10, 0x50, 0x0e, b'c', b'e', b'r', b't', b'2', 0x06, 0x07, 0x08, 0x09, 0x0a,
                0x0b, 0x0c,
                // Hash 1
                0x70, 0x10, 0x00, 0x01, 0x01, 0x02, 0x03, 0x05, 0x08, 0x0d, 0x15, 0x22, 0x37, 0x59,
                0x90, 0xe9,
            ];
            let perso_blob = PersoBlob {
                num_objs: 3,
                next_free: perso_blob_bytes.len(),
                body: perso_blob_bytes.into_iter().collect(),
            };
            let parser = PersoBlobParser::new(perso_blob);
            let mut perso_blob_iterator = parser.iter();

            let first_obj = perso_blob_iterator.next().unwrap().unwrap();
            assert_eq!(first_obj.obj_header.obj_type, ObjType::EndorsedX509Cert);
            assert_eq!(first_obj.obj_header.obj_size, 13);
            assert_eq!(
                first_obj.data,
                &[
                    0x40, 0x0b, b'c', b'e', b'r', b't', 0x01, 0x02, 0x03, 0x04, 0x05
                ]
            );

            let second_obj = perso_blob_iterator.next().unwrap().unwrap();
            assert_eq!(second_obj.obj_header.obj_type, ObjType::EndorsedX509Cert);
            assert_eq!(second_obj.obj_header.obj_size, 16);
            assert_eq!(
                second_obj.data,
                &[
                    0x50, 0x0e, b'c', b'e', b'r', b't', b'2', 0x06, 0x07, 0x08, 0x09, 0x0a, 0x0b,
                    0x0c
                ]
            );

            let third_obj = perso_blob_iterator.next().unwrap().unwrap();
            assert_eq!(third_obj.obj_header.obj_type, ObjType::PersoSha256Hash);
            assert_eq!(third_obj.obj_header.obj_size, 16);
            assert_eq!(
                third_obj.data,
                &[
                    0x00, 0x01, 0x01, 0x02, 0x03, 0x05, 0x08, 0x0d, 0x15, 0x22, 0x37, 0x59, 0x90,
                    0xe9
                ]
            );

            assert!(perso_blob_iterator.next().is_none());
        }

        #[test]
        fn v0_blob_partial_header_iter() {
            #[rustfmt::skip]
            let perso_blob_bytes = vec![
                // Cert 1
                0x10, 0x0d, 0x40, 0x0b, b'c', b'e', b'r', b't', 0x01, 0x02, 0x03, 0x04, 0x05,
                // Cert 2 with partial header
                0x10,
            ];
            let perso_blob = PersoBlob {
                num_objs: 2,
                next_free: perso_blob_bytes.len(),
                body: perso_blob_bytes.into_iter().collect(),
            };
            let parser = PersoBlobParser::new(perso_blob);
            let mut perso_blob_iterator = parser.iter();

            let first_obj = perso_blob_iterator.next().unwrap().unwrap();
            assert_eq!(first_obj.obj_header.obj_type, ObjType::EndorsedX509Cert);
            assert_eq!(first_obj.obj_header.obj_size, 13);
            assert_eq!(
                first_obj.data,
                &[
                    0x40, 0x0b, b'c', b'e', b'r', b't', 0x01, 0x02, 0x03, 0x04, 0x05
                ]
            );

            let second_obj = perso_blob_iterator.next().unwrap();
            assert!(second_obj.is_err());
        }

        #[test]
        fn v0_blob_partial_body_iter() {
            #[rustfmt::skip]
            let perso_blob_bytes = vec![
                // Cert 1
                0x10, 0x0d, 0x40, 0x0b, b'c', b'e', b'r', b't', 0x01, 0x02, 0x03, 0x04, 0x05,
                // Cert 2 with partial body
                0x10, 0x10, 0x50, 0x0e, b'c', b'e',
            ];
            let perso_blob = PersoBlob {
                num_objs: 2,
                next_free: perso_blob_bytes.len(),
                body: perso_blob_bytes.into_iter().collect(),
            };
            let parser = PersoBlobParser::new(perso_blob);
            let mut perso_blob_iterator = parser.iter();

            let first_obj = perso_blob_iterator.next().unwrap().unwrap();
            assert_eq!(first_obj.obj_header.obj_type, ObjType::EndorsedX509Cert);
            assert_eq!(first_obj.obj_header.obj_size, 13);
            assert_eq!(
                first_obj.data,
                &[
                    0x40, 0x0b, b'c', b'e', b'r', b't', 0x01, 0x02, 0x03, 0x04, 0x05
                ]
            );

            let second_obj = perso_blob_iterator.next().unwrap();
            assert!(second_obj.is_err());
        }

        #[test]
        fn v1_blob_iter() {
            #[rustfmt::skip]
            let perso_blob_bytes = vec![
                // Cert 1
                0xf0, 0x04, 0x00, 0x01,
                0x01, 0x00, 0x00, 0x11, 0x04, 0x00, 0x00, 0x0d, b'c', b'e', b'r', b't', 0x01, 0x02,
                0x03, 0x04, 0x05,
                // Cert 2
                0xf0, 0x04, 0x00, 0x01,
                0x01, 0x00, 0x00, 0x14, 0x05, 0x00, 0x00, 0x10, b'c', b'e', b'r', b't', b'2', 0x06,
                0x07, 0x08, 0x09, 0x0a, 0x0b, 0x0c,
                // Hash 1
                0xf0, 0x04, 0x00, 0x01,
                0x07, 0x00, 0x00, 0x12, 0x00, 0x01, 0x01, 0x02, 0x03, 0x05, 0x08, 0x0d, 0x15, 0x22,
                0x37, 0x59, 0x90, 0xe9,
            ];
            let perso_blob = PersoBlob {
                num_objs: 3,
                next_free: perso_blob_bytes.len(),
                body: perso_blob_bytes.into_iter().collect(),
            };
            let parser = PersoBlobParser::new(perso_blob);
            let mut perso_blob_iterator = parser.iter();

            let first_obj = perso_blob_iterator.next().unwrap().unwrap();
            assert_eq!(first_obj.obj_header.obj_type, ObjType::EndorsedX509Cert);
            assert_eq!(first_obj.obj_header.obj_size, 21);
            assert_eq!(
                first_obj.data,
                &[
                    0x04, 0x00, 0x00, 0x0d, b'c', b'e', b'r', b't', 0x01, 0x02, 0x03, 0x04, 0x05
                ]
            );

            let second_obj = perso_blob_iterator.next().unwrap().unwrap();
            assert_eq!(second_obj.obj_header.obj_type, ObjType::EndorsedX509Cert);
            assert_eq!(second_obj.obj_header.obj_size, 24);
            assert_eq!(
                second_obj.data,
                &[
                    0x05, 0x00, 0x00, 0x10, b'c', b'e', b'r', b't', b'2', 0x06, 0x07, 0x08, 0x09,
                    0x0a, 0x0b, 0x0c
                ]
            );

            let third_obj = perso_blob_iterator.next().unwrap().unwrap();
            assert_eq!(third_obj.obj_header.obj_type, ObjType::PersoSha256Hash);
            assert_eq!(third_obj.obj_header.obj_size, 22);
            assert_eq!(
                third_obj.data,
                &[
                    0x00, 0x01, 0x01, 0x02, 0x03, 0x05, 0x08, 0x0d, 0x15, 0x22, 0x37, 0x59, 0x90,
                    0xe9
                ]
            );

            assert!(perso_blob_iterator.next().is_none());
        }

        #[test]
        fn v1_blob_partial_header_iter() {
            #[rustfmt::skip]
            let perso_blob_bytes = vec![
                // Cert 1
                0xf0, 0x04, 0x00, 0x01,
                0x01, 0x00, 0x00, 0x11, 0x04, 0x00, 0x00, 0x0d, b'c', b'e', b'r', b't', 0x01, 0x02,
                0x03, 0x04, 0x05,
                // Cert 2 with partial header
                0xf0, 0x04, 0x00, 0x01,
                0x01, 0x00, 0x00,
            ];
            let perso_blob = PersoBlob {
                num_objs: 2,
                next_free: perso_blob_bytes.len(),
                body: perso_blob_bytes.into_iter().collect(),
            };
            let parser = PersoBlobParser::new(perso_blob);
            let mut perso_blob_iterator = parser.iter();

            let first_obj = perso_blob_iterator.next().unwrap().unwrap();
            assert_eq!(first_obj.obj_header.obj_type, ObjType::EndorsedX509Cert);
            assert_eq!(first_obj.obj_header.obj_size, 21);
            assert_eq!(
                first_obj.data,
                &[
                    0x04, 0x00, 0x00, 0x0d, b'c', b'e', b'r', b't', 0x01, 0x02, 0x03, 0x04, 0x05
                ]
            );

            let second_obj = perso_blob_iterator.next().unwrap();
            assert!(second_obj.is_err());
        }

        #[test]
        fn v1_blob_with_partial_body_iter() {
            #[rustfmt::skip]
            let perso_blob_bytes = vec![
                // Cert 1
                0xf0, 0x04, 0x00, 0x01,
                0x01, 0x00, 0x00, 0x11, 0x04, 0x00, 0x00, 0x0d, b'c', b'e', b'r', b't', 0x01, 0x02,
                0x03, 0x04, 0x05,
                // Cert 2 with partial body
                0xf0, 0x04, 0x00, 0x01,
                0x01, 0x00, 0x00, 0x14, 0x05, 0x00, 0x00, 0x10, b'c', b'e',
            ];
            let perso_blob = PersoBlob {
                num_objs: 2,
                next_free: perso_blob_bytes.len(),
                body: perso_blob_bytes.into_iter().collect(),
            };
            let parser = PersoBlobParser::new(perso_blob);
            let mut perso_blob_iterator = parser.iter();

            let first_obj = perso_blob_iterator.next().unwrap().unwrap();
            assert_eq!(first_obj.obj_header.obj_type, ObjType::EndorsedX509Cert);
            assert_eq!(first_obj.obj_header.obj_size, 21);
            assert_eq!(
                first_obj.data,
                &[
                    0x04, 0x00, 0x00, 0x0d, b'c', b'e', b'r', b't', 0x01, 0x02, 0x03, 0x04, 0x05
                ]
            );

            let second_obj = perso_blob_iterator.next().unwrap();
            assert!(second_obj.is_err());
        }
    }
}
