// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::{bail, Result};
use clap::Parser;
use once_cell::sync::Lazy;
use std::collections::HashMap;
use std::time::Duration;

use opentitanlib::app::TransportWrapper;
use opentitanlib::io::gpio::PinMode;
use opentitanlib::io::uart::Uart;
use opentitanlib::test_utils::init::InitializeTest;
use opentitanlib::test_utils::pinmux_config::PinmuxConfig;
use opentitanlib::test_utils::sysrst_ctrl::SysrstCtrlPin;
use opentitanlib::uart::console::UartConsole;
use opentitanlib::{collection, execute_test};

use opentitanlib::chip::autogen::earlgrey::{PinmuxInsel, PinmuxPeripheralIn};

#[derive(Debug, Parser)]
struct Opts {
    #[command(flatten)]
    init: InitializeTest,

    /// Console receive timeout.
    #[arg(long, value_parser = humantime::parse_duration, default_value = "10s")]
    timeout: Duration,
}

struct IoPin {
    sysrst_pin: SysrstCtrlPin,
    // IO name of the transport
    transport_pin: &'static str,
}

struct Config {
    // List of pinmuxes to configure.
    pinmux: HashMap<PinmuxPeripheralIn, PinmuxInsel>,
    // Map to the IO names of the transport.
    pins: Vec<IoPin>,
}

static CONFIG: Lazy<HashMap<&'static str, Config>> = Lazy::new(|| {
    collection! {
        "hyper310" => Config {
            // See https://github.com/lowRISC/opentitan/blob/master/hw/top_earlgrey/ip/pinmux/doc/autogen/pinout_cw310.md
            pinmux: collection! {
                PinmuxPeripheralIn::SysrstCtrlAonPwrbIn  => PinmuxInsel::Ior2,
                PinmuxPeripheralIn::SysrstCtrlAonKey0In  => PinmuxInsel::Ior3,
                PinmuxPeripheralIn::SysrstCtrlAonKey1In  => PinmuxInsel::Ior4,
                PinmuxPeripheralIn::SysrstCtrlAonKey2In  => PinmuxInsel::Ior5,
                PinmuxPeripheralIn::SysrstCtrlAonLidOpen  => PinmuxInsel::Ior6,
                PinmuxPeripheralIn::SysrstCtrlAonAcPresent => PinmuxInsel::Ior7,
                // SysrstCtrlEcRst is wired to IOR8
                // SysrstCtrlFlashWp is wired to IOR9*/
            },
            pins: vec! {
                IoPin{ sysrst_pin: SysrstCtrlPin::PowerButtonIn, transport_pin: "IOR2" },
                IoPin{ sysrst_pin: SysrstCtrlPin::Key0In, transport_pin: "IOR3" },
                IoPin{ sysrst_pin: SysrstCtrlPin::Key1In, transport_pin: "IOR4" },
                IoPin{ sysrst_pin: SysrstCtrlPin::Key2In, transport_pin: "IOR5" },
                IoPin{ sysrst_pin: SysrstCtrlPin::LidOpenIn, transport_pin: "IOR6" },
                IoPin{ sysrst_pin: SysrstCtrlPin::AcPowerPresentIn, transport_pin: "IOR7" },
                IoPin{ sysrst_pin: SysrstCtrlPin::EcResetInOut, transport_pin: "IOR8" },
                IoPin{ sysrst_pin: SysrstCtrlPin::FlashWriteProtectInOut, transport_pin: "IOR9" },
            }
        },
    }
});

// The value is encoded by an integer whose ith bit represents
// the value of the ith entry in config.pins
// FIXME this might be overkill but allows to have proper Debug format output
// and do some checks
struct PinValues<'a> {
    config: &'a Config,
    values: u32,
}

impl<'a> PinValues<'a> {
    fn new(config: &'a Config) -> Self {
        PinValues {config, values: 0}
    }

    fn is_pin_set(&self, bit_idx: usize) -> bool {
        // FIXME check index here
        ((self.values >> bit_idx) & 1) == 1
    }

    fn set_pin(&mut self, bit_idx: usize) {
        // FIXME check index here
        self.values |= 1u32 << bit_idx;
    }
}

impl std::fmt::Debug for PinValues<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{:b} [", self.values)?;
        for (i, pin) in self.config.pins.iter().enumerate() {
            if self.is_pin_set(i) {
                write!(f, "{:?} ", pin.sysrst_pin)?;
            }
        }
        write!(f, "]")
    }
}

impl PartialEq for PinValues<'_> {
    fn eq(&self, other: &Self) -> bool {
        self.values == other.values
    }
}

/// Configure earlgrey and debugger pins.
fn setup_pins(uart: &dyn Uart, transport: &TransportWrapper, config: &Config) -> Result<()> {
    log::info!("Configuring earlgrey pinmux");
    PinmuxConfig::configure(uart, Some(&config.pinmux), None)?;

    /* On reset, the flash_wp and ec_reset pins, which are inout, have an output override
     * enabled so that they stretch the reset and flash protection during boot. Disable this
     * mecanism.
     * FIXME this seems to have no impact?! */
    SysrstCtrlPin::EcResetInOut.configure_override(
        uart, /* enabled */ false, /* allow_zero */ true, /* allow_one */ true,
        /* override_value */ false,
    )?;
    SysrstCtrlPin::FlashWriteProtectInOut.configure_override(
        uart, /* enabled */ false, /* allow_zero */ true, /* allow_one */ true,
        /* override_value */ false,
    )?;

    log::info!("Configuring debugger GPIOs");
    for pin in config.pins.iter() {
        transport
            .gpio_pin(pin.transport_pin)?
            .set_mode(PinMode::PushPull)?;
    }

    Ok(())
}

fn test_combination(
    uart: &dyn Uart,
    transport: &TransportWrapper,
    config: &Config,
    values: &PinValues,
) -> Result<()> {
    // Set pins on the transport.
    for (i, pin) in config.pins.iter().enumerate() {
        transport
            .gpio_pin(pin.transport_pin)?
            .write(values.is_pin_set(i))?;
    }
    // Read pins on the device.
    let mut sysrst_values = PinValues::new(config);
    for (i, pin) in config.pins.iter().enumerate() {
        if pin.sysrst_pin.read(uart)? {
            sysrst_values.set_pin(i);
        }
    }

    if *values != sysrst_values {
        log::error!("The pin values set on the debugger was:");
        log::error!("{:?}", values);
        log::error!("The pin values reported by sysrst_ctrl was:");
        log::error!("{:?}", sysrst_values);
        bail!("pin value mismatch");
    }
    Ok(())
}

fn chip_sw_sysrst_ctrl_input(
    _opts: &Opts,
    transport: &TransportWrapper,
    config: &Config,
) -> Result<()> {
    let uart = transport.uart("console")?;
    setup_pins(&*uart, transport, config)?;

    test_combination(
        &*uart,
        transport,
        config,
        &PinValues { config, values: 0b10001011 }
    )?;

    Ok(())
}

fn main() -> Result<()> {
    let opts = Opts::parse();
    opts.init.init_logging();
    let transport = opts.init.init_target()?;

    let uart = transport.uart("console")?;
    uart.set_flow_control(true)?;
    let _ = UartConsole::wait_for(&*uart, r"Running [^\r\n]*", opts.timeout)?;

    log::info!(
        "Use pin configuration for {:?}",
        opts.init.backend_opts.interface
    );
    let config = CONFIG
        .get(opts.init.backend_opts.interface.as_str())
        .expect("interface");

    execute_test!(chip_sw_sysrst_ctrl_input, &opts, &transport, config);
    Ok(())
}
