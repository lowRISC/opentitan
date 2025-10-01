// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::Result;

use super::{Backend, BackendOpts, define_interface};
use crate::transport::Transport;
use crate::transport::chip_whisperer::board::{Cw310, Cw340};
use crate::transport::hyperdebug::{
    C2d2Flavor, ChipWhispererFlavor, ServoMicroFlavor, StandardFlavor, Ti50Flavor,
};
use crate::transport::hyperdebug::{Flavor, Hyperdebug, HyperdebugDfu};

struct HyperdebugBackend<T>(T);

impl<T: Flavor + 'static> Backend for HyperdebugBackend<T> {
    type Opts = ();

    fn create_transport(args: &BackendOpts, _: &()) -> Result<Box<dyn Transport>> {
        Ok(Box::new(Hyperdebug::<T>::open(
            args.usb_vid,
            args.usb_pid,
            args.usb_serial.as_deref(),
        )?))
    }
}

define_interface!(
    "hyper310",
    HyperdebugBackend<ChipWhispererFlavor<Cw310>>,
    "/__builtin__/hyperdebug_cw310.json5"
);
define_interface!(
    "hyper340",
    HyperdebugBackend<ChipWhispererFlavor<Cw340>>,
    "/__builtin__/hyperdebug_cw340.json5"
);
define_interface!(
    "teacup",
    HyperdebugBackend<StandardFlavor>,
    "/__builtin__/hyperdebug_teacup_default.json5"
);
define_interface!("hyperdebug", HyperdebugBackend<StandardFlavor>);
define_interface!(
    "c2d2",
    HyperdebugBackend<C2d2Flavor>,
    "/__builtin__/h1dx_devboard_c2d2.json5"
);
define_interface!(
    "servo_micro",
    HyperdebugBackend<ServoMicroFlavor>,
    "/__builtin__/servo_micro.json5"
);
define_interface!("ti50", HyperdebugBackend<Ti50Flavor>);

struct HyperdebugDfuBackend;

impl Backend for HyperdebugDfuBackend {
    type Opts = ();

    fn create_transport(args: &BackendOpts, _: &()) -> Result<Box<dyn Transport>> {
        Ok(Box::new(HyperdebugDfu::open(
            args.usb_vid,
            args.usb_pid,
            args.usb_serial.as_deref(),
        )?))
    }
}

define_interface!("hyperdebug_dfu", HyperdebugDfuBackend);
