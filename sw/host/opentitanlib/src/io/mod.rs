// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

pub mod console;
pub mod eeprom;
pub mod emu;
pub mod gpio;
pub mod i2c;
pub mod io_mapper;
pub mod ioexpander;
pub mod jtag;
pub mod nonblocking_help;
pub mod spi;
pub mod uart;

pub fn merge_configuration_field<T>(f1: &mut Option<T>, f2: &Option<T>) -> Option<()>
where
    T: PartialEq<T> + Clone,
{
    match (&*f1, f2) {
        (Some(v1), Some(v2)) if *v1 != *v2 => return None,
        (None, _) => *f1 = f2.clone(),
        _ => (),
    }
    Some(())
}
