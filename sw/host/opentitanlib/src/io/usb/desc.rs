// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::{Result, anyhow};
use num_enum::{IntoPrimitive, TryFromPrimitive};
use zerocopy::byteorder::little_endian::U16;
use zerocopy::{FromBytes, Immutable, KnownLayout, Unaligned};

#[derive(Copy, Clone, Eq, PartialEq, Debug, TryFromPrimitive, IntoPrimitive)]
#[repr(u8)]
pub enum DescriptorType {
    Device = 1,
    Configuration,
    String,
    Interface,
    Endpoint,
}

#[derive(Copy, Clone, Eq, PartialEq, Debug, TryFromPrimitive, IntoPrimitive)]
#[repr(u8)]
pub enum TransferType {
    Control,
    Isochronous,
    Bulk,
    Interrupt,
}

#[derive(Copy, Clone, Eq, PartialEq, Debug)]
pub enum Direction {
    In,
    Out,
}

#[derive(Clone, FromBytes, KnownLayout, Immutable, Unaligned, Debug)]
#[repr(C)]
pub struct DeviceDescriptor {
    pub length: u8,
    pub desc_type: u8,
    pub usb_version: U16,
    pub class: u8,
    pub subclass: u8,
    pub protocol: u8,
    pub max_pkt_size: u8,
    pub vendor_id: U16,
    pub product_id: U16,
    pub dev_version: U16,
    pub manuf_idx: u8,
    pub product_idx: u8,
    pub serial_idx: u8,
    pub num_config: u8,
}

#[derive(Clone, FromBytes, KnownLayout, Immutable, Unaligned, Debug)]
#[repr(C)]
pub struct ConfigurationDescriptor {
    pub length: u8,
    pub desc_type: u8,
    pub tot_length: U16,
    pub num_intf: u8,
    pub config_val: u8,
    pub str_idx: u8,
    pub attr: u8,
    pub max_power: u8,
}

impl ConfigurationDescriptor {
    pub fn string_index(&self) -> Option<u8> {
        if self.str_idx == 0 {
            None
        } else {
            Some(self.str_idx)
        }
    }
}

#[derive(Clone, FromBytes, KnownLayout, Immutable, Unaligned, Debug)]
#[repr(C)]
pub struct InterfaceDescriptor {
    pub length: u8,
    pub desc_type: u8,
    pub intf_num: u8,
    pub alt_setting: u8,
    pub num_ep: u8,
    pub class: u8,
    pub subclass: u8,
    pub protocol: u8,
    pub str_idx: u8,
}

impl InterfaceDescriptor {
    pub fn string_index(&self) -> Option<u8> {
        if self.str_idx == 0 {
            None
        } else {
            Some(self.str_idx)
        }
    }
}

#[derive(Clone, FromBytes, KnownLayout, Immutable, Unaligned, Debug)]
#[repr(C)]
pub struct EndpointDescriptor {
    pub length: u8,
    pub desc_type: u8,
    pub addr: u8,
    pub attr: u8,
    pub max_pkt_size: U16,
    pub interval: u8,
}

impl EndpointDescriptor {
    pub fn transfer_type(&self) -> TransferType {
        // Conversation cannot fail (all cases are covered).
        (self.attr & 0x3).try_into().unwrap()
    }

    pub fn direction(&self) -> Direction {
        if (self.addr & 0x80) == 0 {
            Direction::Out
        } else {
            Direction::In
        }
    }
}

pub struct Configuration<'a> {
    bytes: &'a [u8],
}

impl<'a> Configuration<'a> {
    pub fn new(bytes: &'a [u8]) -> Self {
        Configuration { bytes }
    }

    /// Return the entire configuration (all descriptors).
    pub fn as_bytes(&self) -> &'a [u8] {
        self.bytes
    }

    /// Return the configuration descriptor.
    pub fn descriptor(&self) -> Result<&'a ConfigurationDescriptor> {
        ConfigurationDescriptor::ref_from_prefix(self.bytes)
            .map(|(desc, _)| desc)
            .map_err(|_err| anyhow!("Cannot parse configuration descriptor"))
    }

    /// Iterate over all interfaces.
    pub fn interface_alt_settings(&'a self) -> impl Iterator<Item = Interface<'a>> {
        DescOffsetIter { bytes: self.bytes }.filter_map(|(_, desc_type, bytes)| {
            if desc_type == u8::from(DescriptorType::Interface) {
                Some(Interface { bytes })
            } else {
                None
            }
        })
    }
}

struct DescOffsetIter<'a> {
    bytes: &'a [u8],
}

impl<'a> Iterator for DescOffsetIter<'a> {
    /// (descriptor size, descriptor type, slice)
    type Item = (usize, u8, &'a [u8]);

    fn next(&mut self) -> Option<Self::Item> {
        // We need at least two bytes to get the type of this descriptor.
        if self.bytes.len() < 2 {
            None
        } else {
            let sz = self.bytes[0] as usize;
            let next = Some((sz, self.bytes[1], self.bytes));
            self.bytes = if sz < self.bytes.len() {
                &self.bytes[sz..]
            } else {
                &[]
            };
            next
        }
    }
}

pub struct Interface<'a> {
    bytes: &'a [u8],
}

impl<'a> Interface<'a> {
    /// Return the interface's descriptor.
    pub fn descriptor(&self) -> Result<&'a InterfaceDescriptor> {
        InterfaceDescriptor::ref_from_prefix(self.bytes)
            .map(|(desc, _)| desc)
            .map_err(|_err| anyhow!("Cannot parse interface descriptor"))
    }

    fn subdescriptor_iter(&self) -> impl Iterator<Item = (usize, u8, &'a [u8])> {
        DescOffsetIter { bytes: self.bytes }
            .skip(1)
            .take_while(|(_, desc_type, _)| {
                // Stop when we reach the next interface.
                *desc_type != u8::from(DescriptorType::Interface)
            })
    }

    /// Iterate over all endpoints.
    pub fn endpoints(&self) -> impl Iterator<Item = Endpoint<'a>> {
        self.subdescriptor_iter()
            .filter_map(|(_, desc_type, bytes)| {
                if desc_type == u8::from(DescriptorType::Endpoint) {
                    Some(Endpoint { bytes })
                } else {
                    None
                }
            })
    }

    pub fn subdescriptors(&self) -> impl Iterator<Item = &'a [u8]> {
        self.subdescriptor_iter().filter_map(|(sz, _, bytes)| {
            // Ignore invalid descriptors (size would go beyond end of buffer).
            if sz <= bytes.len() {
                Some(&bytes[..sz])
            } else {
                None
            }
        })
    }
}

pub struct Endpoint<'a> {
    bytes: &'a [u8],
}

impl<'a> Endpoint<'a> {
    pub fn descriptor(&self) -> Result<&'a EndpointDescriptor> {
        EndpointDescriptor::ref_from_prefix(self.bytes)
            .map(|(desc, _)| desc)
            .map_err(|_err| anyhow!("Cannot parse endpoint descriptor"))
    }
}
