// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use std::cmp;
use std::collections::HashMap;
use std::time::Duration;

use anyhow::Result;

use ot_hal::dif::pinmux::PinmuxPadAttr;
use ot_hal::top::earlgrey::{PinmuxInsel, PinmuxMioOut, PinmuxOutsel, PinmuxPeripheralIn};

use crate::io::uart::Uart;
use crate::test_utils::e2e_command::TestCommand;
use crate::test_utils::rpc::{ConsoleRecv, ConsoleSend};
use crate::test_utils::status::Status;

// Create aliases for the C names of these types so that the ujson
// created structs can access these structures by their C names.
#[allow(non_camel_case_types)]
type pinmux_peripheral_in_t = PinmuxPeripheralIn;
#[allow(non_camel_case_types)]
type pinmux_insel_t = PinmuxInsel;
#[allow(non_camel_case_types)]
type pinmux_mio_out_t = PinmuxMioOut;
#[allow(non_camel_case_types)]
type pinmux_outsel_t = PinmuxOutsel;

// Bring in the auto-generated sources.
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
            Status::recv(uart, Duration::from_secs(300), false, false)?;
        }

        Ok(())
    }
}
