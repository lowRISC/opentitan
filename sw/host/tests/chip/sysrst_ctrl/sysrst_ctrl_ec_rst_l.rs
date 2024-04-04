// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::{bail, ensure, Result};
use clap::Parser;
use once_cell::sync::Lazy;
use std::borrow::Borrow;
use std::rc::Rc;
use std::time::Duration;

use opentitanlib::app::TransportWrapper;
use opentitanlib::execute_test;
use opentitanlib::io::gpio::{ClockNature, Edge, MonitoringEvent, PinMode};
use opentitanlib::io::uart::Uart;
use opentitanlib::test_utils::init::InitializeTest;
use opentitanlib::test_utils::test_status::TestStatus;
use opentitanlib::uart::console::UartConsole;

use sysrst_ctrl::{read_pins, set_pins, setup_pins, Config};

#[derive(Debug, Parser)]
struct Opts {
    #[command(flatten)]
    init: InitializeTest,

    /// Console receive timeout.
    #[arg(long, value_parser = humantime::parse_duration, default_value = "10s")]
    timeout: Duration,
}

struct Params<'a> {
    opts: &'a Opts,
    transport: &'a TransportWrapper,
    uart: &'a dyn Uart,
    config: &'a Config,
}

static CONFIG: Lazy<Config> = Lazy::new(|| {
    Config {
        // key0_in, key1_in
        output_pins: vec!["IOR6", "IOR7"],
        open_drain: vec![false, false],
        // ec_rst, flash_wp
        input_pins: vec!["SYSRST_CTRL_EC_RST_L", "SYSRST_CTRL_FLASH_WP_L"],
        // ec_rst, flash_wp
        pullup_pins: vec!["SYSRST_CTRL_EC_RST_L", "SYSRST_CTRL_FLASH_WP_L"],
    }
});

const COMBO_PINS_HIGH: u8 = 0x3;
const COMBO_PINS_LOW: u8 = 0;
const COMBO_PINS_KEY0_HIGH: u8 = 1;
const EC_RST_FLASH_WP_HIGH: u8 = 0x3;
const EC_RST_PIN_INDEX: u8 = 0;
const FLASH_WP_PIN_INDEX: u8 = 1;
const EC_RST_PIN: &str = "IOR8";

const EC_RST_COMBO_PULSE_WIDTH_USEC: u64 = 100_000; // Set on the device.
const EC_RST_STRETCH_PULSE_WIDTH_USEC: u64 = 200_000; // Set on the device.
const EC_RST_PULE_WIDTH_MARGIN_USEC: u64 = 5_000;

fn sync_with_sw(params: &Params) -> Result<()> {
    UartConsole::wait_for(
        params.uart,
        &TestStatus::InWfi.wait_pattern(),
        params.opts.timeout,
    )?;
    Ok(())
}

fn chip_sw_sysrst_ctrl_input(params: &Params) -> Result<()> {
    // Setup transport pins.
    setup_pins(params.transport, params.config)?;
    // Set combo pins to high.
    set_pins(params.transport, params.config, COMBO_PINS_HIGH)?;

    // Reset target now so that we can be sure that the pins are in the right
    // configuration before running the test.
    params
        .transport
        .reset_target(params.opts.init.bootstrap.options.reset_delay, true)?;

    // Wait until device has setup pins and is waiting for combo.
    sync_with_sw(params)?;
    // On POR, the device releases the EC_RST and FLASH_WP pins.
    ensure!(read_pins(params.transport, params.config)? == EC_RST_FLASH_WP_HIGH);

    // We are going to set the combo pins to low and monitor the GPIO.
    let gpio_monitoring = params.transport.gpio_monitoring()?;
    let clock_nature = gpio_monitoring.get_clock_nature()?;
    let ClockNature::Wallclock { resolution, .. } = clock_nature else {
        bail!("Cannot measure EC reset pulse width: the transport GPIO monitor does not have reliable clock source");
    };
    log::info!("GPIO monitor clock resolution: {resolution}");
    let gpio_pins = &params
        .config
        .input_pins
        .iter()
        .map(|x| x.to_string())
        .collect::<Vec<_>>();
    let gpio_pins = params.transport.gpio_pins(gpio_pins)?;
    let gpios_pins = &gpio_pins.iter().map(Rc::borrow).collect::<Vec<_>>();
    let start_resp = gpio_monitoring.monitoring_start(gpios_pins)?;
    // The initial levels should match the pins: all ones.
    ensure!(!start_resp.initial_levels.iter().any(|level| !level));

    // Set combo pins to low which triggers the combo and resets the device.
    set_pins(params.transport, params.config, COMBO_PINS_LOW)?;
    // Wait until device has rebooted and is waiting for our signal.
    sync_with_sw(params)?;
    // Wait for a short time just to make sure that the EC reset line stays down.
    std::thread::sleep(Duration::from_millis(500));
    // Stop monitoring and check that ec_rst and flash_wp were held low during
    // the entire time.
    let events = gpio_monitoring.monitoring_read(gpios_pins, false)?;
    for event in &events.events {
        log::info!("{event:?}");
    }
    let mut events_iter = events.events.iter();
    let Some(first_event) = events_iter.next() else {
        bail!("Expected at least one GPIO event during reset");
    };
    let Some(second_event) = events_iter.next() else {
        bail!("Expected at least two GPIO events during reset");
    };
    if let Some(third_event) = events_iter.next() {
        bail!("Unexpected third GPIO event during reset: {third_event:?}");
    }
    match (first_event, second_event) {
        (
            &MonitoringEvent {
                signal_index: first_index,
                edge: Edge::Falling,
                ..
            },
            &MonitoringEvent {
                signal_index: second_index,
                edge: Edge::Falling,
                ..
            },
        ) => {
            // Sanity check: make sure each pin (ec_rst and flash_wp) is now low.
            ensure!(
                (first_index == EC_RST_PIN_INDEX && second_index == FLASH_WP_PIN_INDEX)
                    || (first_index == FLASH_WP_PIN_INDEX && second_index == EC_RST_PIN_INDEX)
            );
        }
        _ => bail!(
            "the GPIO events do not match what was expected: {first_event:?}, {second_event:?}"
        ),
    }
    // Set key0 to high to continue the test.
    set_pins(params.transport, params.config, COMBO_PINS_KEY0_HIGH)?;
    // In reponse, the device should release the pins.
    sync_with_sw(params)?;
    ensure!(read_pins(params.transport, params.config)? == EC_RST_FLASH_WP_HIGH);

    // Exercise the EC reset pulse: pull ec_rst low and then high, measure how long
    // it is held low.
    let start_resp = gpio_monitoring.monitoring_start(gpios_pins)?;
    // The initial levels should be all ones.
    ensure!(!start_resp.initial_levels.iter().any(|level| !level));
    // Change the EC_RST pin to output, pull low and reset to input.
    params
        .transport
        .gpio_pin(EC_RST_PIN)?
        .set_mode(PinMode::OpenDrain)?;
    params.transport.gpio_pin(EC_RST_PIN)?.write(false)?;
    std::thread::sleep(Duration::from_millis(1));
    params.transport.gpio_pin(EC_RST_PIN)?.write(true)?;
    // We expect OT to pulse EC for a while, so wait with some margin.
    std::thread::sleep(
        Duration::from_micros(EC_RST_COMBO_PULSE_WIDTH_USEC) + Duration::from_millis(100),
    );
    // Stop monitoring.
    let events = gpio_monitoring.monitoring_read(gpios_pins, false)?;
    // We expect to see EC_RST go low and then high.
    let mut events_iter = events.events.iter();
    let Some(first_event) = events_iter.next() else {
        bail!("Expected at least one GPIO event during reset");
    };
    let Some(second_event) = events_iter.next() else {
        bail!("Expected at least two GPIO events during reset");
    };
    if let Some(third_event) = events_iter.next() {
        bail!("Unexpected third GPIO event during reset: {third_event:?}");
    }
    match (first_event, second_event) {
        (
            &MonitoringEvent {
                signal_index: EC_RST_PIN_INDEX,
                edge: Edge::Falling,
                timestamp: fall_timestamp,
            },
            &MonitoringEvent {
                signal_index: EC_RST_PIN_INDEX,
                edge: Edge::Rising,
                timestamp: rise_timestamp,
            },
        ) => {
            // Convert a timestamp in transport unit to something in nanoseconds.
            let timestamp_to_ns =
                |timestamp: u64| -> u64 { timestamp * 1000000000u64 / resolution };
            // Make sure the pulse width matches what we expect.
            let pulse_width_us =
                (timestamp_to_ns(rise_timestamp) - timestamp_to_ns(fall_timestamp)) / 1000;
            let delta = EC_RST_STRETCH_PULSE_WIDTH_USEC.abs_diff(pulse_width_us);
            log::info!("reset pulse width =  {pulse_width_us} us, delta = {delta} us");
            ensure!(delta <= EC_RST_PULE_WIDTH_MARGIN_USEC);
        }
        _ => bail!(
            "the GPIO events do not match what was expected: {first_event:?}, {second_event:?}"
        ),
    }

    // Wait until device has done its work.
    let _ = UartConsole::wait_for(params.uart, r"PASS!", params.opts.timeout)?;

    Ok(())
}

fn main() -> Result<()> {
    let opts = Opts::parse();
    opts.init.init_logging();
    let transport = opts.init.init_target()?;

    let uart = transport.uart("console")?;
    uart.set_flow_control(true)?;
    let _ = UartConsole::wait_for(&*uart, r"Running [^\r\n]*", opts.timeout)?;

    execute_test!(
        chip_sw_sysrst_ctrl_input,
        &Params {
            opts: &opts,
            transport: &transport,
            uart: &*uart,
            config: &CONFIG,
        }
    );
    Ok(())
}
