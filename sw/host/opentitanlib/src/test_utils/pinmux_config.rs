// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use std::cmp;
use std::collections::HashMap;
use std::time::Duration;

use anyhow::Result;

use crate::chip::autogen::earlgrey::{PinmuxInsel, PinmuxMioOut, PinmuxOutsel, PinmuxPeripheralIn};
use crate::dif::pinmux::PinmuxPadAttr;
use crate::io::uart::Uart;
use crate::test_utils::e2e_command::TestCommand;
use crate::test_utils::rpc::{UartRecv, UartSend};
use crate::test_utils::status::Status;

// Bring in the auto-generated sources.
use crate::chip::autogen::earlgrey::ujson_alias::*;
include!(env!("pinmux_config"));

/// Capacity of a single configuration message.
const CONFIG_CAP: usize = 16;

impl PinmuxConfig {
    pub fn configure(
        uart: &dyn Uart,
        inputs: Option<&HashMap<PinmuxPeripheralIn, PinmuxInsel>>,
        outputs: Option<&HashMap<PinmuxMioOut, PinmuxOutsel>>,
        attrs: Option<&HashMap<PinmuxMioOut, PinmuxPadAttr>>,
    ) -> Result<()> {
        // The PinmuxConfig struct can carry a limited number of input
        // and output configurations.  We'll take the whole config and
        // chunk it into as many PinmuxConfig commands as necessary.

        let mut inputs: Vec<_> = inputs
            .into_iter()
            .flat_map(HashMap::iter)
            .map(|(&key, &value)| (key, value))
            .collect();
        let mut outputs: Vec<_> = outputs
            .into_iter()
            .flat_map(HashMap::iter)
            .map(|(&key, &value)| (key, value))
            .collect();
        let mut attrs: Vec<_> = attrs
            .into_iter()
            .flat_map(HashMap::iter)
            .map(|(&key, &value)| (key, value.bits()))
            .collect();

        let len = cmp::max(cmp::max(inputs.len(), outputs.len()), attrs.len())
            .next_multiple_of(CONFIG_CAP);

        inputs.resize_with(len, Default::default);
        outputs.resize_with(len, Default::default);
        attrs.resize_with(len, Default::default);

        while !inputs.is_empty() && !outputs.is_empty() && !attrs.is_empty() {
            let (in_peripherals, in_selectors) = inputs.drain(..CONFIG_CAP).unzip();
            let (out_mios, out_selectors) = outputs.drain(..CONFIG_CAP).unzip();
            let (attr_mios, attr_flags) = attrs.drain(..CONFIG_CAP).unzip();

            let config = PinmuxConfig {
                input: PinmuxInputSelection {
                    peripheral: in_peripherals,
                    selector: in_selectors,
                },
                output: PinmuxOutputSelection {
                    mio: out_mios,
                    selector: out_selectors,
                },
                attrs: PinmuxAttrConfig {
                    mio: attr_mios,
                    flags: attr_flags,
                },
            };

            TestCommand::PinmuxConfig.send(uart)?;
            config.send(uart)?;
            Status::recv(uart, Duration::from_secs(300), false)?;
        }

        Ok(())
    }
}
