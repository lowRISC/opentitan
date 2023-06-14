// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::{ensure, Result};
use once_cell::sync::Lazy;
use std::cell::RefCell;
use std::collections::HashMap;
use std::rc::Rc;

use crate::collection;
use crate::io::gpio::{GpioError, GpioPin, PinMode, PullMode};
use crate::transport::dediprog::Inner;
use crate::util::parse_int::ParseInt;

pub struct DediprogPin {
    inner: Rc<RefCell<Inner>>,
    index: u8,
}

impl DediprogPin {
    const LAST_PIN_NUM: u8 = 15;

    pub fn open(inner: Rc<RefCell<Inner>>, pinname: &str) -> Result<Self> {
        Ok(Self {
            inner,
            index: Self::pin_name_to_number(pinname)?,
        })
    }

    /// Given an ultradebug pin name, return its pin number.
    pub fn pin_name_to_number(pinname: &str) -> Result<u8> {
        // If the pinname is an integer, use it; otherwise try to see if it
        // is a symbolic name of a pin.
        if let Ok(pinnum) = u8::from_str(pinname) {
            ensure!(
                pinnum <= Self::LAST_PIN_NUM,
                GpioError::InvalidPinNumber(pinnum)
            );
            return Ok(pinnum);
        }
        let pinname = pinname.to_uppercase();
        let pn = pinname.as_str();
        PIN_NAMES
            .get(pn)
            .copied()
            .ok_or_else(|| GpioError::InvalidPinName(pinname).into())
    }
}

impl GpioPin for DediprogPin {
    fn read(&self) -> Result<bool> {
        Ok(self.inner.borrow().gpio_levels & (1 << self.index) != 0)
    }

    fn write(&self, value: bool) -> Result<()> {
        let mut inner = self.inner.borrow_mut();
        if value {
            inner.gpio_levels |= 1u16 << self.index
        } else {
            inner.gpio_levels &= !(1u16 << self.index)
        }
        inner.set_gpio_levels()
    }

    fn set_mode(&self, mode: PinMode) -> Result<()> {
        match mode {
            PinMode::PushPull => Ok(()),
            _ => Err(GpioError::UnsupportedPinMode(mode).into()),
        }
    }

    fn set_pull_mode(&self, mode: PullMode) -> Result<()> {
        match mode {
            PullMode::None => Ok(()),
            _ => Err(GpioError::UnsupportedPullMode(mode).into()),
        }
    }
}

static PIN_NAMES: Lazy<HashMap<&'static str, u8>> = Lazy::new(|| {
    collection! {
        "IO2" => 0,
        "IO1" => 1,
        "IO3" => 2,
        "IO4" => 3,
        "PASS_LED" => 8,
        "BUSY_LED" => 9,
        "ERROR_LED" => 10,
    }
});
