// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::Result;
use std::collections::HashMap;
use std::time::Duration;

use crate::chip::autogen::earlgrey::{PinmuxInsel, PinmuxMioOut, PinmuxOutsel, PinmuxPeripheralIn};
use crate::io::uart::Uart;
use crate::test_utils::e2e_command::TestCommand;
use crate::test_utils::rpc::{ConsoleRecv, ConsoleSend};
use crate::test_utils::status::Status;

// Bring in the auto-generated sources.
use crate::chip::autogen::earlgrey::ujson_alias::*;
include!(env!("pinmux_config"));

impl Default for PinmuxConfig {
    fn default() -> Self {
        Self {
            input: PinmuxInputSelection {
                peripheral: Default::default(),
                selector: Default::default(),
            },
            output: PinmuxOutputSelection {
                mio: Default::default(),
                selector: Default::default(),
            },
        }
    }
}

impl PinmuxConfig {
    pub fn configure(
        uart: &dyn Uart,
        inputs: Option<&HashMap<PinmuxPeripheralIn, PinmuxInsel>>,
        outputs: Option<&HashMap<PinmuxMioOut, PinmuxOutsel>>,
    ) -> Result<()> {
        // The PinmuxConfig struct can carry a limited number of input
        // and output configurations.  We'll take the whole config and
        // chunk it into as many PinmuxConfig commands as necessary.

        let len = std::cmp::max(
            inputs.map(|h| h.len()).unwrap_or(0),
            outputs.map(|h| h.len()).unwrap_or(0),
        );

        let df_ik = PinmuxPeripheralIn::default();
        let df_iv = PinmuxInsel::default();
        let df_ok = PinmuxMioOut::default();
        let df_ov = PinmuxOutsel::default();

        let mut inputs = inputs.map(|h| h.iter());
        let mut outputs = outputs.map(|h| h.iter());
        let mut i = 0;
        while i < len {
            let mut config = Self::default();
            for _ in 0..config.input.peripheral.capacity() {
                let (ik, iv) = inputs
                    .as_mut()
                    .and_then(|i| i.next())
                    .unwrap_or((&df_ik, &df_iv));
                let (ok, ov) = outputs
                    .as_mut()
                    .and_then(|i| i.next())
                    .unwrap_or((&df_ok, &df_ov));
                config.input.peripheral.push(*ik);
                config.input.selector.push(*iv);
                config.output.mio.push(*ok);
                config.output.selector.push(*ov);
                i += 1;
            }
            TestCommand::PinmuxConfig.send(uart)?;
            config.send(uart)?;
            Status::recv(uart, Duration::from_secs(300), false)?;
        }
        Ok(())
    }
}
