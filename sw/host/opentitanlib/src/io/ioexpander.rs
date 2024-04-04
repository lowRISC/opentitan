// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use std::rc::Rc;

use crate::io::gpio::GpioPin;

pub struct IoExpander {
    pub pins: Vec<Rc<dyn GpioPin>>,
}
