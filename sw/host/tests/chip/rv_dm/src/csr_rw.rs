// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use std::time::Duration;

use anyhow::{ensure, Context, Result};
use clap::Parser;
use rand::prelude::*;

use opentitanlib::app::TransportWrapper;
use opentitanlib::execute_test;
use opentitanlib::io::jtag::{Jtag, JtagTap};
use opentitanlib::test_utils::init::InitializeTest;
use opentitanlib::uart::console::UartConsole;

use bindgen::dif;
use top_earlgrey::top_earlgrey;

#[derive(Debug, Parser)]
struct Opts {
    #[command(flatten)]
    init: InitializeTest,

    #[arg(long)]
    rv_dm_delayed_enable: bool,

    /// Seed for random number generator.
    #[arg(long)]
    seed: Option<u64>,

    /// Console receive timeout.
    #[arg(long, value_parser = humantime::parse_duration, default_value = "100s")]
    timeout: Duration,
}

fn test(jtag: &mut dyn Jtag, base: usize, offset: u32) -> Result<()> {
    let addr = base as u32 + offset;

    let mut old_value = 0;
    jtag.read_memory32(addr, std::slice::from_mut(&mut old_value))?;

    let new_value = old_value ^ 1;
    jtag.write_memory32(addr, &[new_value])?;
    let mut readback = 0;
    jtag.read_memory32(addr, std::slice::from_mut(&mut readback))?;
    ensure!(new_value == readback);

    jtag.write_memory32(addr, &[old_value])?;
    jtag.read_memory32(addr, std::slice::from_mut(&mut readback))?;
    ensure!(old_value == readback);

    Ok(())
}

fn test_csr_rw(opts: &Opts, transport: &TransportWrapper) -> Result<()> {
    let seed = opts.seed.unwrap_or_else(|| thread_rng().gen());
    log::info!("Random number generator seed is {:x}", seed);
    let mut rng = rand_chacha::ChaCha12Rng::seed_from_u64(seed);

    transport.pin_strapping("PINMUX_TAP_RISCV")?.apply()?;
    transport.reset_target(opts.init.bootstrap.options.reset_delay, true)?;
    let uart = &*transport.uart("console")?;
    uart.set_flow_control(true)?;

    if opts.rv_dm_delayed_enable {
        UartConsole::wait_for(uart, r"DEBUG_MODE_ENABLED", opts.timeout)?;
    } else {
        // Avoid watchdog timeout by entering bootstrap mode.
        transport.pin_strapping("ROM_BOOTSTRAP")?.apply()?;
        transport.reset_target(opts.init.bootstrap.options.reset_delay, true)?;
    }

    let jtag = &mut *opts
        .init
        .jtag_params
        .create(transport)?
        .connect(JtagTap::RiscvTap)?;

    let mut tests = [
        ("aes", top_earlgrey::AES_BASE_ADDR, dif::AES_IV_0_REG_OFFSET),
        (
            "adc_ctrl",
            top_earlgrey::ADC_CTRL_AON_BASE_ADDR,
            dif::ADC_CTRL_INTR_ENABLE_REG_OFFSET,
        ),
        (
            "alert_handler",
            top_earlgrey::ALERT_HANDLER_BASE_ADDR,
            dif::ALERT_HANDLER_INTR_ENABLE_REG_OFFSET,
        ),
        (
            "aon_timer",
            top_earlgrey::AON_TIMER_AON_BASE_ADDR,
            dif::AON_TIMER_WKUP_CTRL_REG_OFFSET,
        ),
        (
            "csrng",
            top_earlgrey::CSRNG_BASE_ADDR,
            dif::CSRNG_INTR_ENABLE_REG_OFFSET,
        ),
        (
            "edn0",
            top_earlgrey::EDN0_BASE_ADDR,
            dif::EDN_INTR_ENABLE_REG_OFFSET,
        ),
        (
            "edn1",
            top_earlgrey::EDN1_BASE_ADDR,
            dif::EDN_INTR_ENABLE_REG_OFFSET,
        ),
        (
            "entropy_src",
            top_earlgrey::ENTROPY_SRC_BASE_ADDR,
            dif::ENTROPY_SRC_INTR_ENABLE_REG_OFFSET,
        ),
        (
            "flash_ctrl",
            top_earlgrey::FLASH_CTRL_CORE_BASE_ADDR,
            dif::FLASH_CTRL_INTR_ENABLE_REG_OFFSET,
        ),
        (
            "gpio",
            top_earlgrey::GPIO_BASE_ADDR,
            dif::GPIO_INTR_ENABLE_REG_OFFSET,
        ),
        (
            "hmac",
            top_earlgrey::HMAC_BASE_ADDR,
            dif::HMAC_INTR_ENABLE_REG_OFFSET,
        ),
        (
            "i2c0",
            top_earlgrey::I2C0_BASE_ADDR,
            dif::I2C_INTR_ENABLE_REG_OFFSET,
        ),
        (
            "i2c1",
            top_earlgrey::I2C1_BASE_ADDR,
            dif::I2C_INTR_ENABLE_REG_OFFSET,
        ),
        (
            "i2c2",
            top_earlgrey::I2C2_BASE_ADDR,
            dif::I2C_INTR_ENABLE_REG_OFFSET,
        ),
        (
            "keymgr",
            top_earlgrey::KEYMGR_BASE_ADDR,
            dif::KEYMGR_INTR_ENABLE_REG_OFFSET,
        ),
        (
            "kmac",
            top_earlgrey::KMAC_BASE_ADDR,
            dif::KMAC_INTR_ENABLE_REG_OFFSET,
        ),
        (
            "otbn",
            top_earlgrey::OTBN_BASE_ADDR,
            dif::OTBN_INTR_ENABLE_REG_OFFSET,
        ),
        (
            "otp_ctrl",
            top_earlgrey::OTP_CTRL_CORE_BASE_ADDR,
            dif::OTP_CTRL_INTR_ENABLE_REG_OFFSET,
        ),
        (
            "pattgen",
            top_earlgrey::PATTGEN_BASE_ADDR,
            dif::PATTGEN_INTR_ENABLE_REG_OFFSET,
        ),
        (
            "pinmux",
            top_earlgrey::PINMUX_AON_BASE_ADDR,
            dif::PINMUX_MIO_PAD_ATTR_0_REG_OFFSET,
        ),
        (
            "pwm",
            top_earlgrey::PWM_AON_BASE_ADDR,
            dif::PWM_INVERT_REG_OFFSET,
        ),
        (
            "pwrmgr",
            top_earlgrey::PWRMGR_AON_BASE_ADDR,
            dif::PWRMGR_INTR_ENABLE_REG_OFFSET,
        ),
        // Skip ROM_CTRL which does not have RW registers
        (
            "rstmgr",
            top_earlgrey::RSTMGR_AON_BASE_ADDR,
            dif::RSTMGR_CPU_INFO_CTRL_REG_OFFSET,
        ),
        (
            "rv_timer",
            top_earlgrey::RV_TIMER_BASE_ADDR,
            dif::RV_TIMER_INTR_ENABLE0_REG_OFFSET,
        ),
        (
            "sensor_ctrl",
            top_earlgrey::SENSOR_CTRL_AON_BASE_ADDR,
            dif::SENSOR_CTRL_INTR_ENABLE_REG_OFFSET,
        ),
        (
            "spi_device",
            top_earlgrey::SPI_DEVICE_BASE_ADDR,
            dif::SPI_DEVICE_INTR_ENABLE_REG_OFFSET,
        ),
        (
            "spi_host0",
            top_earlgrey::SPI_HOST0_BASE_ADDR,
            dif::SPI_HOST_INTR_ENABLE_REG_OFFSET,
        ),
        (
            "spi_host1",
            top_earlgrey::SPI_HOST1_BASE_ADDR,
            dif::SPI_HOST_INTR_ENABLE_REG_OFFSET,
        ),
        (
            "sysrst_ctrl",
            top_earlgrey::SYSRST_CTRL_AON_BASE_ADDR,
            dif::SYSRST_CTRL_INTR_ENABLE_REG_OFFSET,
        ),
        (
            "uart0",
            top_earlgrey::UART0_BASE_ADDR,
            dif::UART_INTR_ENABLE_REG_OFFSET,
        ),
        (
            "uart1",
            top_earlgrey::UART1_BASE_ADDR,
            dif::UART_INTR_ENABLE_REG_OFFSET,
        ),
        (
            "uart2",
            top_earlgrey::UART2_BASE_ADDR,
            dif::UART_INTR_ENABLE_REG_OFFSET,
        ),
        (
            "uart3",
            top_earlgrey::UART3_BASE_ADDR,
            dif::UART_INTR_ENABLE_REG_OFFSET,
        ),
        (
            "usbdev",
            top_earlgrey::USBDEV_BASE_ADDR,
            dif::USBDEV_INTR_ENABLE_REG_OFFSET,
        ),
    ];

    tests.shuffle(&mut rng);

    for (name, base, offset) in tests.iter().copied() {
        log::info!("Testing {}", name);
        test(jtag, base, offset).with_context(|| format!("{} test failed", name))?;
    }

    Ok(())
}

fn main() -> Result<()> {
    let opts = Opts::parse();
    opts.init.init_logging();
    let transport = opts.init.init_target()?;

    execute_test!(test_csr_rw, &opts, &transport);

    Ok(())
}
