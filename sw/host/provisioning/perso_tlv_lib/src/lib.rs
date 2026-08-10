// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use core::{
    convert::{Into, TryFrom, TryInto},
    iter::Iterator,
    marker::Copy,
    num::TryFromIntError,
    option_env,
};

use arrayvec::ArrayVec;
use perso_tlv_objects::perso_tlv_blob_version_payload;
use ujson_lib::provisioning_data::PersoBlob;

use anyhow::{Result, bail};

type BlobVersionType = u16;

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

impl TryFrom<ObjType> for u32 {
    type Error = TryFromIntError;
    fn try_from(value: ObjType) -> Result<Self, Self::Error> {
        Self::try_from(value as usize)
    }
}

impl ObjType {
    pub fn from_usize(value: usize) -> Result<ObjType> {
        match value {
            0 => Ok(ObjType::UnendorsedX509Cert),
            1 => Ok(ObjType::EndorsedX509Cert),
            2 => Ok(ObjType::DevSeed),
            3 => Ok(ObjType::EndorsedCwtCert),
            4 => Ok(ObjType::WasTbsHmac),
            5 => Ok(ObjType::DeviceId),
            6 => Ok(ObjType::GenericSeed),
            7 => Ok(ObjType::PersoSha256Hash),
            15 => Ok(ObjType::PersoBlobVersion),
            _ => bail!("incorrect input value of {value} for ObjType"),
        }
    }
}

// Header of the LTV object
#[derive(Debug, Copy, Clone)]
pub struct ObjHeader {
    pub obj_size: usize,
    pub obj_type: ObjType,
}

// Header and body of the certificate payload of the LTV object
pub struct CertWithHeader<'a> {
    // Total size the certificate takes in the buffer, header + hame length +
    // cert size.
    pub wrapped_size: usize,
    pub cert_name: &'a str,
    pub cert_body: Vec<u8>,
}

pub struct PersoBlobBuilder {
    data: ArrayVec<u8, 5120>,
    version: SupportedPersoTlvVersion,
    num_objs: usize,
}

impl PersoBlobBuilder {
    pub fn new_with_version(version: u16) -> Result<Self> {
        match version {
            0 => Ok(Self {
                data: ArrayVec::new(),
                version: SupportedPersoTlvVersion::V0,
                num_objs: 0,
            }),
            1 => {
                let mut data = ArrayVec::new();
                let perso_blob_version_obj_bytes =
                    PersoBlobVersionObj::new(1).into_perso_blob_bytes()?;
                data.try_extend_from_slice(&perso_blob_version_obj_bytes)?;
                Ok(Self {
                    data,
                    version: SupportedPersoTlvVersion::V1,
                    num_objs: 1,
                })
            }
            _ => bail!("Unsupported version {version}"),
        }
    }

    pub fn push_endorsed_cert(&mut self, cert: &Vec<u8>, ref_cert: &CertWithHeader) -> Result<()> {
        let mut data: Vec<u8> = vec![];
        match self.version {
            SupportedPersoTlvVersion::V0 => {
                let (obj_header, cert_header) =
                    PersoTlvTypesV0::make_obj_and_endorsed_cert_headers(
                        cert.len(),
                        ref_cert.cert_name,
                    )?;
                data.extend(&obj_header.to_be_bytes());
                data.extend(&cert_header.to_be_bytes());
            }
            SupportedPersoTlvVersion::V1 => {
                let (obj_header, cert_header) =
                    PersoTlvTypesV1::make_obj_and_endorsed_cert_headers(
                        cert.len(),
                        ref_cert.cert_name,
                    )?;
                data.extend(&obj_header.to_be_bytes());
                data.extend(&cert_header.to_be_bytes());
            }
        }
        data.extend(ref_cert.cert_name.as_bytes());
        data.extend(cert.as_slice());
        self.data.try_extend_from_slice(&data)?;
        self.num_objs += 1;

        Ok(())
    }

    pub fn into_perso_blob(self) -> PersoBlob {
        PersoBlob {
            num_objs: self.num_objs,
            next_free: self.data.len(),
            body: self.data,
        }
    }
}

pub struct PersoBlobParser {
    perso_blob: PersoBlob,
    version: SupportedPersoTlvVersion,
}

impl PersoBlobParser {
    pub fn new_with_version(version: u16, perso_blob: PersoBlob) -> Result<Self> {
        // For v1 (and hopefully other new versions), the first TLV entry will be a
        // BlobVersion TLV object (ref
        // https://github.com/lowRISC/opentitan/blob/c99009d5a3a011de401404479ff823e636f170ce/sw/device/silicon_creator/manuf/base/ft_personalize.c#L558-L566). This is formatted using v0 TLV format for backwards compatibility
        // For v0, this TLV object will not be present

        match PersoBlobVersionObj::from_perso_blob(&perso_blob)? {
            None => {
                // This is a v0 Perso Blob
                if version > 0 {
                    bail!(
                        "Perso blob version {version} expected, but there is no PersoBlobVersion TLV object in the beginning"
                    )
                }
                return Ok(Self {
                    perso_blob,
                    version: SupportedPersoTlvVersion::V0,
                });
            }
            Some(obj) => {
                // This is a Perso blob with non-zero version
                if version == 0 {
                    bail!(
                        "Perso blob has PersoBlobVersion TLV object with version {} in the beginning, but expected version is 0",
                        obj.version
                    );
                }
                if version != obj.version {
                    bail!(
                        "Perso blob version {} is different from the requested version {version}",
                        obj.version
                    )
                }
                match version {
                    1 => {
                        return Ok(Self {
                            perso_blob,
                            version: SupportedPersoTlvVersion::V1,
                        });
                    }
                    _ => bail!("Unsupported Perso blob version {version}"),
                }
            }
        }
    }

    pub fn get_obj_header(&self, data: &[u8]) -> Result<ObjHeader> {
        match self.version {
            SupportedPersoTlvVersion::V0 => PersoTlvTypesV0::get_obj_header(data),
            SupportedPersoTlvVersion::V1 => PersoTlvTypesV1::get_obj_header(data),
        }
    }

    pub fn get_obj_header_size(&self) -> usize {
        match self.version {
            SupportedPersoTlvVersion::V0 => {
                std::mem::size_of::<<PersoTlvTypesV0 as PersoTlvTypes>::ObjHeaderType>()
            }
            SupportedPersoTlvVersion::V1 => {
                std::mem::size_of::<<PersoTlvTypesV1 as PersoTlvTypes>::ObjHeaderType>()
            }
        }
    }

    pub fn get_cert<'a>(&self, data: &'a [u8]) -> Result<CertWithHeader<'a>> {
        match self.version {
            SupportedPersoTlvVersion::V0 => PersoTlvTypesV0::get_cert(data),
            SupportedPersoTlvVersion::V1 => PersoTlvTypesV1::get_cert(data),
        }
    }

    pub fn iter(&self) -> PersoBlobIterator<'_> {
        match self.version {
            SupportedPersoTlvVersion::V0 => PersoBlobIterator::new(self, 0, 0),
            SupportedPersoTlvVersion::V1 => PersoBlobIterator::new(self, 1, 4),
        }
    }
}

pub struct PersoBlobObject<'a> {
    pub obj_header: ObjHeader,
    pub data: &'a [u8],
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
        let obj_header: ObjHeader = match self.parser.get_obj_header(remaining_data) {
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

        let obj_header_size = self.parser.get_obj_header_size();
        Some(Ok(PersoBlobObject {
            obj_header,
            data: &remaining_data[obj_header_size..][..obj_header.obj_size - obj_header_size],
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

    const ObjhSizeFieldMask: u32;
    const ObjhSizeFieldShift: u32;
    const ObjhTypeFieldMask: u32;
    const ObjhTypeFieldShift: u32;

    const CrthSizeFieldMask: u32;
    const CrthSizeFieldShift: u32;
    const CrthNameSizeFieldMask: u32;
    const CrthNameSizeFieldShift: u32;

    // Expects that `val` is Host-Endian
    fn get_obj_size(val: Self::ObjHeaderType) -> usize {
        return usize::try_from((val.into() >> Self::ObjhSizeFieldShift) & Self::ObjhSizeFieldMask)
            .expect("ObjhSize must fit in usize");
    }

    // Expects that `val` is Host-Endian
    fn get_obj_type_raw_value(val: Self::ObjHeaderType) -> usize {
        return usize::try_from((val.into() >> Self::ObjhTypeFieldShift) & Self::ObjhTypeFieldMask)
            .expect("ObjhType must fit in usize");
    }

    // Expects that `val` is Host-Endian
    fn get_crth_size(val: Self::CertHeaderType) -> usize {
        return usize::try_from((val.into() >> Self::CrthSizeFieldShift) & Self::CrthSizeFieldMask)
            .expect("CrthSize must fit in usize");
    }

    // Expects that `val` is Host-Endian
    fn get_crth_name_size(val: Self::CertHeaderType) -> usize {
        return usize::try_from(
            (val.into() >> Self::CrthNameSizeFieldShift) & Self::CrthNameSizeFieldMask,
        )
        .expect("CrthNameSize must fit in usize");
    }

    // Extract LTV object header from the input buffer.
    fn get_obj_header(data: &[u8]) -> Result<ObjHeader> {
        let header_len = std::mem::size_of::<Self::ObjHeaderType>();

        if data.len() < header_len {
            bail!(
                "Insufficient amount of data ({} bytes) for object header. Needs {} bytes",
                data.len(),
                header_len
            )
        }

        let obj_header = Self::ObjHeaderType::from_be_bytes(data)?;
        let obj_size = Self::get_obj_size(obj_header);
        let obj_type = Self::get_obj_type_raw_value(obj_header);

        if obj_size > data.len() {
            bail!(
                "Object {} length {} exceeds buffer size {}",
                obj_type,
                obj_size,
                data.len()
            );
        }

        if obj_size < header_len {
            bail!(
                "Object {} length {} is less than Object header length {}",
                obj_type,
                obj_size,
                header_len
            );
        }

        let obj_type = ObjType::from_usize(obj_type)?;
        Ok(ObjHeader { obj_type, obj_size })
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

        let cert_header = Self::CertHeaderType::from_be_bytes(&data)?;
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
    fn make_obj_header(size: usize, otype: ObjType) -> Result<Self::ObjHeaderType> {
        let size = u32::try_from(size)?;
        let otype = u32::try_from(otype)?;
        if size > Self::ObjhSizeFieldMask {
            bail!("Can't create object of size {size}")
        }

        let obj_size_val = (size & Self::ObjhSizeFieldMask) << Self::ObjhSizeFieldShift;
        let obj_type_val = (otype & Self::ObjhTypeFieldMask) << Self::ObjhTypeFieldShift;
        let obj_header_val = obj_size_val | obj_type_val;

        Self::ObjHeaderType::try_from(obj_header_val)
            .map_err(|_| anyhow::anyhow!("Failed to create ObjHeader from {obj_header_val}"))
    }

    fn make_obj_and_endorsed_cert_headers(
        cert_size: usize,
        cert_name: &str,
    ) -> Result<(Self::ObjHeaderType, Self::CertHeaderType)> {
        let total_obj_size = std::mem::size_of::<Self::ObjHeaderType>()
            + std::mem::size_of::<Self::CertHeaderType>()
            + cert_name.len()
            + cert_size;

        let cert_size = u32::try_from(cert_size)?;
        let name_len = u32::try_from(cert_name.len())?;

        if name_len > Self::CrthNameSizeFieldMask {
            bail!(
                "Can't create certificate wrapper for name \"{}\"",
                cert_name
            )
        }

        let wrapped_size =
            cert_size + name_len + u32::try_from(std::mem::size_of::<Self::CertHeaderType>())?;
        if wrapped_size > Self::CrthSizeFieldMask {
            bail!("Can't create a certificate wrapper of size {wrapped_size}")
        }

        let cert_size_val = (wrapped_size & Self::CrthSizeFieldMask) << Self::CrthSizeFieldShift;
        let cert_name_size_val =
            (name_len & Self::CrthNameSizeFieldMask) << Self::CrthNameSizeFieldShift;
        let cert_header_val = cert_size_val | cert_name_size_val;

        let cert_header = Self::CertHeaderType::try_from(cert_header_val)
            .map_err(|_| anyhow::anyhow!("Failed to create CertHeader from {cert_header_val}"))?;
        let obj_header = Self::make_obj_header(total_obj_size, ObjType::EndorsedX509Cert)?;

        Ok((obj_header, cert_header))
    }
}

struct PersoTlvTypesV0;
struct PersoTlvTypesV1;

impl PersoTlvTypes for PersoTlvTypesV0 {
    type ObjHeaderType = perso_tlv_objects::perso_tlv_object_header_t;
    type CertHeaderType = perso_tlv_objects::perso_tlv_cert_header_t;

    const ObjhSizeFieldMask: u32 =
        perso_tlv_objects::perso_tlv_obj_header_fields_v0_kObjhSizeFieldMaskV0;
    const ObjhSizeFieldShift: u32 =
        perso_tlv_objects::perso_tlv_obj_header_fields_v0_kObjhSizeFieldShiftV0;
    const ObjhTypeFieldMask: u32 =
        perso_tlv_objects::perso_tlv_obj_header_fields_v0_kObjhTypeFieldMaskV0;
    const ObjhTypeFieldShift: u32 =
        perso_tlv_objects::perso_tlv_obj_header_fields_v0_kObjhTypeFieldShiftV0;

    const CrthSizeFieldMask: u32 =
        perso_tlv_objects::perso_tlv_cert_header_fields_v0_kCrthSizeFieldMaskV0;
    const CrthSizeFieldShift: u32 =
        perso_tlv_objects::perso_tlv_cert_header_fields_v0_kCrthSizeFieldShiftV0;
    const CrthNameSizeFieldMask: u32 =
        perso_tlv_objects::perso_tlv_cert_header_fields_v0_kCrthNameSizeFieldMaskV0;
    const CrthNameSizeFieldShift: u32 =
        perso_tlv_objects::perso_tlv_cert_header_fields_v0_kCrthNameSizeFieldShiftV0;
}

impl PersoTlvTypes for PersoTlvTypesV1 {
    type ObjHeaderType = perso_tlv_objects::perso_tlv_object_header_v1_t;
    type CertHeaderType = perso_tlv_objects::perso_tlv_cert_header_v1_t;

    const ObjhSizeFieldMask: u32 =
        perso_tlv_objects::perso_tlv_obj_header_fields_v1_kObjhSizeFieldMaskV1;
    const ObjhSizeFieldShift: u32 =
        perso_tlv_objects::perso_tlv_obj_header_fields_v1_kObjhSizeFieldShiftV1;
    const ObjhTypeFieldMask: u32 =
        perso_tlv_objects::perso_tlv_obj_header_fields_v1_kObjhTypeFieldMaskV1;
    const ObjhTypeFieldShift: u32 =
        perso_tlv_objects::perso_tlv_obj_header_fields_v1_kObjhTypeFieldShiftV1;

    const CrthSizeFieldMask: u32 =
        perso_tlv_objects::perso_tlv_cert_header_fields_v1_kCrthSizeFieldMaskV1;
    const CrthSizeFieldShift: u32 =
        perso_tlv_objects::perso_tlv_cert_header_fields_v1_kCrthSizeFieldShiftV1;
    const CrthNameSizeFieldMask: u32 =
        perso_tlv_objects::perso_tlv_cert_header_fields_v1_kCrthNameSizeFieldMaskV1;
    const CrthNameSizeFieldShift: u32 =
        perso_tlv_objects::perso_tlv_cert_header_fields_v1_kCrthNameSizeFieldShiftV1;
}

enum SupportedPersoTlvVersion {
    V0,
    V1,
}

#[repr(C)]
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

impl PersoBlobVersionObj {
    pub fn new(version: u16) -> Self {
        Self { version }
    }

    pub fn from_perso_blob(blob: &PersoBlob) -> Result<Option<Self>> {
        if blob.body.is_empty() {
            // Assume empty PersoBlob to be V0
            return Ok(None);
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
            return Ok(Some(Self {
                version: u16::from_be_bytes(blob.body[obj_header_size..][..2].try_into()?),
            }));
        }
        Ok(None)
    }

    pub fn into_perso_blob_bytes(self) -> Result<Vec<u8>> {
        let obj_header_size =
            std::mem::size_of::<<PersoTlvTypesV0 as PersoTlvTypes>::ObjHeaderType>();
        let mut data = PersoTlvTypesV0::make_obj_header(
            (std::mem::size_of::<Self>() + obj_header_size),
            ObjType::PersoBlobVersion,
        )?
        .to_be_bytes()
        .to_vec();
        data.extend(&self.version.to_be_bytes());
        Ok(data)
    }
}
