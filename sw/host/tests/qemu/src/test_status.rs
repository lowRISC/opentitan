// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

//! Test harness which starts QEMU and waits for it to pass.
//!
//! Uses QEMU's log interface which prints `PASSED` or `FAILED` when the test
//! status register is written rather than checking the UART. This is compatible
//! with lower-level tests not using the UART, for example `rom_exit_immediately`.

use std::time::Duration;

use anyhow::anyhow;
use clap::Parser;
use opentitanlib::backend::qemu::QemuOpts;
use opentitanlib::transport::Transport;
use opentitanlib::transport::qemu::Qemu;
use opentitanlib::uart::console::UartConsole;

#[derive(Debug, Parser)]
struct Opts {
    #[command(flatten)]
    qemu_opts: QemuOpts,

    #[arg(long, default_value_t)]
    rcfile: String,

    #[arg(long, default_value_t)]
    logging: String,

    #[arg(long, default_value_t)]
    interface: String,
}

fn main() -> anyhow::Result<()> {
    let opts = Opts::parse();
    let qemu = Qemu::from_options(opts.qemu_opts)?;

    let mut monitor = qemu.monitor.borrow_mut();

    monitor.cont()?;

    let log = qemu.uart("log")?;
    let res = UartConsole::wait_for(&*log, "PASSED|FAILED", Duration::from_secs(60))?;
    match res[0].as_str() {
        "PASSED" => Ok(()),
        "FAILED" => Err(anyhow!("QEMU reported failure")),
        _ => unreachable!(),
    }
}
