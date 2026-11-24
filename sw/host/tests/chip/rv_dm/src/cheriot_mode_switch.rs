// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

//! Host side of the RV DM CHERIoT mode switch test.

use std::time::Duration;

use anyhow::{Context, Result, ensure};
use clap::Parser;
use rand::prelude::*;

use opentitanlib::app::{TransportWrapper, UartRx};
use opentitanlib::debug::dmi::{Dmi, DmiDebugger, DmiHart, OpenOcdDmi, consts};
use opentitanlib::execute_test;
use opentitanlib::io::uart::Uart;
use opentitanlib::test_utils::init::InitializeTest;
use opentitanlib::uart::console::UartConsole;

#[derive(Debug, Parser)]
struct Opts {
    #[command(flatten)]
    init: InitializeTest,

    /// Console receive timeout.
    #[arg(long, value_parser = humantime::parse_duration, default_value = "60s")]
    timeout: Duration,
}

// Needs to match util/openocd/target
const RISCV_IDCODE: u32 = 0x10021cdf;

// Abstract command fields, for an Access Register command (cmdtype 0).
const AARSIZE_SHIFT: u32 = 20;
const TRANSFER: u32 = 1 << 17;
const WRITE: u32 = 1 << 16;
const AARSIZE_32: u32 = 2;
const AARSIZE_64: u32 = 3;

// The abstract command written is not supported.
const CMDERR_NOT_SUPPORTED: u32 = 2;
// The abstract command written is supported and was attempted,
// but an exception was raised. This error code must be returned
// if an unimplemented register was attempted to be accessed.
const CMDERR_EXCEPTION: u32 = 3;

// In CHERIoT mode, Abstract registers 0-0x1f now become the SCRs,
// which support 64-bit accesses. The rest of the CSR range (0x20-0xfff)
// is still accessible providing the target CSR exists, but do not support
// 64-bit accesses. There are no CSRs within the range 0-0x1f on Ibex, so
// 32-bit accesses to this range always cause an exception.
#[allow(dead_code)]
const ABSTRACT_REGNO_SCR_FIRST: u32 = 0x0;
const ABSTRACT_REGNO_SCR_DSCRATCH0: u32 = 0x19;
const ABSTRACT_REGNO_SCR_DSCRATCH1: u32 = 0x1a;
const ABSTRACT_REGNO_SCR_MTCC: u32 = 0x1c;
const ABSTRACT_REGNO_SCR_MTDC: u32 = 0x1d;
const ABSTRACT_REGNO_SCR_MSCRATCHC: u32 = 0x1e;
const ABSTRACT_REGNO_SCR_MEPCC: u32 = 0x1f;
#[allow(dead_code)]
const ABSTRACT_REGNO_SCR_LAST: u32 = 0x1f;

// The Abstract register number range 0-0xfff corresponds to the CSRs.
// In RV32 and CHERIoT mode, implemented CSRs are accessible and support up to 32-bit accesses.
// In CHERIoT mode, the `mtvec` and `mepc` CSR numbers become inaccessible,
// as they have been replaced with `mtcc` and `mepcc` respectively.
// In CHERIoT mode, the `mshwm` and `mshwmb` CSRs become accessible.
// `mscratch` and `mtval` remains accessible in both RV32 and CHERIoT.
const ABSTRACT_REGNO_CSR_FIRST: u32 = 0x0;
const ABSTRACT_REGNO_CSR_MTVEC: u32 = 0x305;
const ABSTRACT_REGNO_CSR_MSCRATCH: u32 = 0x340;
const ABSTRACT_REGNO_CSR_MEPC: u32 = 0x341;
const ABSTRACT_REGNO_CSR_MTVAL: u32 = 0x343;
const ABSTRACT_REGNO_CSR_DSCRATCH0: u32 = 0x7b2;
const ABSTRACT_REGNO_CSR_DSCRATCH1: u32 = 0x7b3;
const ABSTRACT_REGNO_CSR_MSHWM: u32 = 0xbc1;
const ABSTRACT_REGNO_CSR_MSHWMB: u32 = 0xbc2;
const ABSTRACT_REGNO_CSR_LAST: u32 = 0xfff;

// The abstract register number range 0x1000-0x101f corresponds to the GPRs x0-x31.
// In RV32 mode, the whole range is accessible, and supports up to 32-bit accesses.
// In CHERIoT mode, there are half the number of GPRs, so only 0x1000-0x100f (x0-x15)
// are accessible, and support up to 64-bit accesses (value and metadata halves).
const ABSTRACT_REGNO_GPR_FIRST: u32 = 0x1000;
const ABSTRACT_REGNO_GPR_LAST_CHERIOT: u32 = 0x100f;
const ABSTRACT_REGNO_GPR_LAST: u32 = 0x101f;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct Cap {
    addr: u32,
    meta: u32,
}

/// Encode a `cgettag rd, cs1` instruction.
fn inst_cgettag(rd: u32, cs1: u32) -> Result<u32> {
    ensure!(rd < 16, "instruction rd out of range");
    ensure!(cs1 < 16, "instruction cs1 out of range");
    Ok((0x7f << 25) | (0x4 << 20) | (cs1 << 15) | (rd << 7) | 0x5b)
}

/// Issue an Access Register command and return `cmderr`, clearing it if it is set.
fn do_access_register_command<D: Dmi>(
    hart: &mut DmiHart<'_, D>,
    regno: u32,
    aarsize: u32,
    write: bool,
) -> Result<u32> {
    let cmd = aarsize << AARSIZE_SHIFT | TRANSFER | if write { WRITE } else { 0 } | regno;
    hart.dmi_write(consts::COMMAND, cmd)?;

    // The command completes when the hart has run it and re-entered the debug ROM. Allow plenty of
    // polls: each one is a JTAG round trip, so this is not the limiting factor.
    let mut abstractcs = hart.dmi_read(consts::ABSTRACTCS)?;
    for _ in 0..100 {
        if abstractcs & consts::ABSTRACTCS_BUSY_MASK == 0 {
            break;
        }
        abstractcs = hart.dmi_read(consts::ABSTRACTCS)?;
    }
    ensure!(
        abstractcs & consts::ABSTRACTCS_BUSY_MASK == 0,
        "abstract command {cmd:#010x} still busy after timeout"
    );

    let cmderr = (abstractcs & consts::ABSTRACTCS_CMDERR_MASK) >> consts::ABSTRACTCS_CMDERR_SHIFT;
    if cmderr != consts::ABSTRACTCS_CMDERR_NONE {
        // cmderr is write-1-to-clear.
        hart.dmi_write(consts::ABSTRACTCS, consts::ABSTRACTCS_CMDERR_MASK)?;
    }
    Ok(cmderr)
}

fn abstract_read_reg<D: Dmi>(hart: &mut DmiHart<'_, D>, regno: u32) -> Result<u32> {
    let cmderr = do_access_register_command(hart, regno, AARSIZE_32, false)?;
    ensure!(
        cmderr == 0,
        "32-bit read of regno {regno:#x} failed with cmderr {cmderr}"
    );
    hart.data(0)
}

fn abstract_read_reg_expect_err<D: Dmi>(
    hart: &mut DmiHart<'_, D>,
    regno: u32,
    expected_cmderr: u32,
) -> Result<()> {
    let cmderr = do_access_register_command(hart, regno, AARSIZE_32, false)?;
    ensure!(
        cmderr == expected_cmderr,
        "32-bit read of regno {regno:#x} unexpectedly succeeded/failed with different cmderr {cmderr}"
    );
    Ok(())
}

fn abstract_write_reg<D: Dmi>(hart: &mut DmiHart<'_, D>, regno: u32, value: u32) -> Result<()> {
    hart.set_data(0, value)?;
    let cmderr = do_access_register_command(hart, regno, AARSIZE_32, true)?;
    ensure!(
        cmderr == 0,
        "32-bit write of regno {regno:#x} failed with cmderr {cmderr}"
    );
    Ok(())
}

fn abstract_write_reg_expect_err<D: Dmi>(
    hart: &mut DmiHart<'_, D>,
    regno: u32,
    expected_cmderr: u32,
) -> Result<()> {
    let cmderr = do_access_register_command(hart, regno, AARSIZE_32, true)?;
    ensure!(
        cmderr == expected_cmderr,
        "32-bit write of regno {regno:#x} unexpectedly succeeded/failed with different cmderr {cmderr}"
    );
    Ok(())
}

fn abstract_read_cap<D: Dmi>(hart: &mut DmiHart<'_, D>, regno: u32) -> Result<Cap> {
    let cmderr = do_access_register_command(hart, regno, AARSIZE_64, false)?;
    ensure!(
        cmderr == 0,
        "64-bit read of regno {regno:#x} failed with cmderr {cmderr}"
    );
    Ok(Cap {
        addr: hart.data(0)?,
        meta: hart.data(1)?,
    })
}

fn abstract_read_cap_expect_err<D: Dmi>(
    hart: &mut DmiHart<'_, D>,
    regno: u32,
    expected_cmderr: u32,
) -> Result<()> {
    let cmderr = do_access_register_command(hart, regno, AARSIZE_64, false)?;
    ensure!(
        cmderr == expected_cmderr,
        "64-bit read of regno {regno:#x} unexpectedly succeeded/failed with different cmderr {cmderr}"
    );
    Ok(())
}

fn abstract_write_cap_expect_err<D: Dmi>(
    hart: &mut DmiHart<'_, D>,
    regno: u32,
    expected_cmderr: u32,
) -> Result<()> {
    let cmderr = do_access_register_command(hart, regno, AARSIZE_64, true)?;
    ensure!(
        cmderr == expected_cmderr,
        "64-bit write of regno {regno:#x} unexpectedly succeeded/failed with different cmderr {cmderr}"
    );
    Ok(())
}

fn abstract_write_cap<D: Dmi>(hart: &mut DmiHart<'_, D>, regno: u32, cap: Cap) -> Result<()> {
    hart.set_data(0, cap.addr)?;
    hart.set_data(1, cap.meta)?;
    let cmderr = do_access_register_command(hart, regno, AARSIZE_64, true)?;
    ensure!(
        cmderr == 0,
        "64-bit write of regno {regno:#x} failed with cmderr {cmderr}"
    );
    Ok(())
}

fn halt<D: Dmi>(hart: &mut DmiHart<'_, D>) -> Result<()> {
    log::info!("Halting hart");
    hart.set_halt_request(true)?;
    hart.wait_halt()?;
    hart.set_halt_request(false)
}

fn resume<D: Dmi>(hart: &mut DmiHart<'_, D>, regno: u32) -> Result<()> {
    log::info!("Resuming hart");
    ensure!(
        ((ABSTRACT_REGNO_GPR_FIRST + 1)..=ABSTRACT_REGNO_GPR_LAST).contains(&regno),
        "Invalid synchronisation register regno {regno:x}"
    );
    ensure!(
        abstract_read_reg(hart, regno)? == 0,
        "register regno {regno:x} should be 0 at this synchronisation point"
    );
    abstract_write_reg(hart, regno, 1)?;

    hart.set_resume_request(true)?;
    hart.wait_resume()?;
    hart.set_resume_request(false)
}

fn wait_for_value(uart: &dyn Uart, timeout: Duration) -> Result<u32> {
    let value = UartConsole::wait_for(uart, "([0-9a-f]{8})", timeout)
        .with_context(|| "waiting for the hart to send register value")?;
    Ok(u32::from_str_radix(&value[0], 16)?)
}

fn wait_for_cap(uart: &dyn Uart, timeout: Duration) -> Result<Cap> {
    let cap = UartConsole::wait_for(uart, r"([0-9a-f]{8})-([0-9a-f]{8})", timeout)
        .with_context(|| "waiting for the device to send capability value")?;
    Ok(Cap {
        addr: u32::from_str_radix(&cap[1], 16)?,
        meta: u32::from_str_radix(&cap[2], 16)?,
    })
}

fn test_rv_dm_mode_switch(opts: &Opts, transport: &TransportWrapper) -> Result<()> {
    let mut rng = rand_chacha::ChaCha12Rng::seed_from_u64(RISCV_IDCODE as u64);

    transport.pin_strapping("PINMUX_TAP_RISCV")?.apply()?;
    transport.reset(UartRx::Clear)?;

    let uart = &*transport.uart("console")?;
    UartConsole::wait_for(uart, r"DM READY", opts.timeout)?;

    let mut openocd = opts.init.jtag_params.create(transport)?.into_raw()?;
    assert_eq!(
        openocd.execute(&format!(
            "jtag newtap riscv tap -irlen 5 -expected-id {RISCV_IDCODE:#x}"
        ))?,
        ""
    );
    assert_eq!(openocd.execute("init")?, "");
    let mut dmi = DmiDebugger::new(OpenOcdDmi::new(openocd, "riscv.tap")?);
    let mut hart = dmi.select_hart(0)?;
    hart.set_dmcontrol(consts::DMCONTROL_ACKHAVERESET_MASK)?;

    {
        halt(&mut hart)?;
        resume(&mut hart, ABSTRACT_REGNO_GPR_FIRST + 1)?;
    }

    UartConsole::wait_for(uart, r"VALUES x0\-x15", opts.timeout)?;

    let mut values = Vec::new();
    for _ in 0..16 {
        values.push(wait_for_value(uart, opts.timeout)?);
    }

    UartConsole::wait_for(uart, r"READY", opts.timeout)?;
    {
        halt(&mut hart)?;

        log::info!("Testing reads of GPRs x0-x15");
        for (i, expected) in values.iter().enumerate().take(16) {
            let regno = ABSTRACT_REGNO_GPR_FIRST + (i as u32);
            ensure!(
                abstract_read_reg(&mut hart, regno)? == *expected,
                format!("incorrect register value for regno {regno:#x}!"),
            );
        }

        log::info!("Testing writes to GPRs x0-x15");
        for i in 1..16 {
            let regno = ABSTRACT_REGNO_GPR_FIRST + (i as u32);
            let value = 0x1;
            abstract_write_reg(&mut hart, regno, value)?;
            ensure!(
                abstract_read_reg(&mut hart, regno)? == value,
                "incorrect 32-bit read value after 32-bit write!"
            );
        }

        resume(&mut hart, ABSTRACT_REGNO_GPR_FIRST + 16)?;
    }

    UartConsole::wait_for(uart, r"VALUES x16\-x31", opts.timeout)?;

    let mut values = Vec::new();
    for _ in 0..16 {
        values.push(wait_for_value(uart, opts.timeout)?);
    }

    UartConsole::wait_for(uart, r"READY", opts.timeout)?;

    {
        halt(&mut hart)?;

        log::info!("Testing reads of GPRs x16-x31");
        for (i, expected) in values.iter().enumerate().take(16) {
            let regno = ABSTRACT_REGNO_GPR_FIRST + 16 + (i as u32);
            ensure!(
                abstract_read_reg(&mut hart, regno)? == *expected,
                format!("incorrect register value for regno {regno:#x}!"),
            );
        }

        log::info!("Testing writes to GPRs x16-x31");
        for i in 0..16 {
            let regno = ABSTRACT_REGNO_GPR_FIRST + 16 + (i as u32);
            let value = 0x1;
            abstract_write_reg(&mut hart, regno, value)?;
            ensure!(
                abstract_read_reg(&mut hart, regno)? == value,
                "incorrect 32-bit read value after 32-bit write!"
            );
        }

        resume(&mut hart, ABSTRACT_REGNO_GPR_FIRST + 1)?;
    }

    UartConsole::wait_for(uart, r"VALUES CSRs", opts.timeout)?;

    let values = [
        (
            ABSTRACT_REGNO_CSR_MSCRATCH,
            wait_for_value(uart, opts.timeout)?,
        ),
        (ABSTRACT_REGNO_CSR_MEPC, wait_for_value(uart, opts.timeout)?),
        (
            ABSTRACT_REGNO_CSR_MTVAL,
            wait_for_value(uart, opts.timeout)?,
        ),
        (
            ABSTRACT_REGNO_CSR_MTVEC,
            wait_for_value(uart, opts.timeout)?,
        ),
    ];

    UartConsole::wait_for(uart, r"READY", opts.timeout)?;

    {
        halt(&mut hart)?;

        log::info!("Testing reads from CSRs mscratch, mepc, mtval, mtvec");
        for (regno, expected) in values {
            let read = abstract_read_reg(&mut hart, regno)?;
            ensure!(
                read == expected,
                format!("incorrect register value for regno {regno:#x}!"),
            );
        }

        // Check that attempting to perform capability-sized accesses
        // is not supported in RV32 mode.
        log::info!("Checking that 64-bit access to GPRs in RV32 is unsupported");
        for regno in ABSTRACT_REGNO_GPR_FIRST..=ABSTRACT_REGNO_GPR_LAST {
            abstract_read_cap_expect_err(&mut hart, regno, CMDERR_NOT_SUPPORTED)?;
            abstract_write_cap_expect_err(&mut hart, regno, CMDERR_NOT_SUPPORTED)?;
        }

        log::info!(
            "Checking that 64-bit access to CSRs in RV32 is unsupported (may take a while...)"
        );
        for regno in ABSTRACT_REGNO_CSR_FIRST..=ABSTRACT_REGNO_CSR_LAST {
            abstract_read_cap_expect_err(&mut hart, regno, CMDERR_NOT_SUPPORTED)?;
            abstract_write_cap_expect_err(&mut hart, regno, CMDERR_NOT_SUPPORTED)?;
        }

        // Check that attempting to access the debug scratch CSRs succeeds.
        log::info!("Testing access to CSRs dscratch0, dscratch1");
        for regno in [ABSTRACT_REGNO_CSR_DSCRATCH0, ABSTRACT_REGNO_CSR_DSCRATCH1] {
            let value = abstract_read_reg(&mut hart, regno)?;
            abstract_write_reg(&mut hart, regno, value)?;
        }

        // Check that attempting to access CSRs that are only
        // implemented in CHERIoT mode causes an exception.
        log::info!("Checking that accessing CSRS mshwm, mshwmb in RV32 causes exceptions");
        for regno in [ABSTRACT_REGNO_CSR_MSHWM, ABSTRACT_REGNO_CSR_MSHWMB] {
            abstract_read_reg_expect_err(&mut hart, regno, CMDERR_EXCEPTION)?;
            abstract_write_reg_expect_err(&mut hart, regno, CMDERR_EXCEPTION)?;
        }

        abstract_read_reg_expect_err(&mut hart, ABSTRACT_REGNO_GPR_LAST + 1, CMDERR_EXCEPTION)?;

        resume(&mut hart, ABSTRACT_REGNO_GPR_FIRST + 1)?;
    }

    log::info!("waiting for CHERIoT mode switch...");

    UartConsole::wait_for(uart, r"CHERIoT READY", opts.timeout)?;

    {
        halt(&mut hart)?;

        resume(&mut hart, ABSTRACT_REGNO_GPR_FIRST + 1)?;
    }

    UartConsole::wait_for(uart, r"VALUES c0-c7", opts.timeout)?;

    let mut caps = Vec::new();
    for _ in 0..8 {
        caps.push(wait_for_cap(uart, opts.timeout)?);
    }

    UartConsole::wait_for(uart, r"READY", opts.timeout)?;

    {
        halt(&mut hart)?;

        log::info!("Testing 32-bit and 64-bit reads of capability GPRs c0-c7");
        for (i, expected) in caps.iter().enumerate().take(8) {
            let regno = ABSTRACT_REGNO_GPR_FIRST + (i as u32);

            ensure!(
                abstract_read_cap(&mut hart, regno)? == *expected,
                format!("incorrect register value for regno {regno:#x}!"),
            );

            ensure!(
                abstract_read_reg(&mut hart, regno)? == expected.addr,
                format!("incorrect register value for regno {regno:#x}!"),
            );
        }

        log::info!("Testing 32-bit and 64-bit writes of capability GPRs c0-c7");
        for i in 1..8 {
            let regno = ABSTRACT_REGNO_GPR_FIRST + (i as u32);

            for _ in 0..16 {
                let value = rng.r#gen::<u32>();
                abstract_write_reg(&mut hart, regno, value)?;

                ensure!(
                    abstract_read_reg(&mut hart, regno)? == value,
                    "incorrect 32-bit read value after 32-bit write"
                );

                ensure!(
                    abstract_read_cap(&mut hart, regno)?
                        == Cap {
                            addr: value,
                            meta: 0
                        },
                    "incorrect 64-bit read value after 32-bit write!"
                );

                let cap = Cap {
                    addr: rng.r#gen::<u32>(),
                    meta: rng.r#gen::<u32>(),
                };
                abstract_write_cap(&mut hart, regno, cap)?;

                ensure!(
                    abstract_read_reg(&mut hart, regno)? == cap.addr,
                    "incorrect 32-bit read value after 64-bit write!"
                );

                ensure!(
                    abstract_read_cap(&mut hart, regno)? == cap,
                    "incorrect 64-bit read value after 64-bit write!"
                );
            }
        }

        resume(&mut hart, ABSTRACT_REGNO_GPR_FIRST + 8)?;
    }

    UartConsole::wait_for(uart, r"VALUES c8-c15", opts.timeout)?;

    let mut caps = Vec::new();
    for _ in 0..8 {
        caps.push(wait_for_cap(uart, opts.timeout)?);
    }

    UartConsole::wait_for(uart, r"READY", opts.timeout)?;

    {
        halt(&mut hart)?;

        log::info!("Testing 32-bit and 64-bit reads of capability GPRs c8-c15");
        for (i, expected) in caps.iter().enumerate().take(8) {
            let regno = ABSTRACT_REGNO_GPR_FIRST + 8 + (i as u32);

            ensure!(
                abstract_read_cap(&mut hart, regno)? == *expected,
                format!("incorrect register value for regno {regno:#x}!"),
            );

            ensure!(
                abstract_read_reg(&mut hart, regno)? == expected.addr,
                format!("incorrect register value for regno {regno:#x}!"),
            );
        }

        log::info!("Testing 32-bit and 64-bit writes of capability GPRs c8-c15");
        for i in 0..8 {
            let regno = ABSTRACT_REGNO_GPR_FIRST + 8 + (i as u32);

            for _ in 0..16 {
                let value = rng.r#gen::<u32>();
                abstract_write_reg(&mut hart, regno, value)?;

                ensure!(
                    abstract_read_reg(&mut hart, regno)? == value,
                    "incorrect 32-bit read value after 32-bit write"
                );

                ensure!(
                    abstract_read_cap(&mut hart, regno)?
                        == Cap {
                            addr: value,
                            meta: 0
                        },
                    "incorrect 64-bit read value after 32-bit write!"
                );

                let cap = Cap {
                    addr: rng.r#gen::<u32>(),
                    meta: rng.r#gen::<u32>(),
                };
                abstract_write_cap(&mut hart, regno, cap)?;

                ensure!(
                    abstract_read_reg(&mut hart, regno)? == cap.addr,
                    "incorrect 32-bit read value after 64-bit write!"
                );

                ensure!(
                    abstract_read_cap(&mut hart, regno)? == cap,
                    "incorrect 64-bit read value after 64-bit write!"
                );
            }
        }

        resume(&mut hart, ABSTRACT_REGNO_GPR_FIRST + 1)?;
    }

    UartConsole::wait_for(uart, r"VALUES SCRs", opts.timeout)?;

    let values = [
        (
            ABSTRACT_REGNO_SCR_MSCRATCHC,
            wait_for_cap(uart, opts.timeout)?,
        ),
        (ABSTRACT_REGNO_SCR_MEPCC, wait_for_cap(uart, opts.timeout)?),
    ];

    let mtval = wait_for_value(uart, opts.timeout)?;

    UartConsole::wait_for(uart, r"READY", opts.timeout)?;

    {
        halt(&mut hart)?;

        log::info!("Testing 32-bit and 64-bit reads from SCRs mscratchc, mepcc");
        for (regno, expected) in values {
            ensure!(
                abstract_read_cap(&mut hart, regno)? == expected,
                format!("incorrect register value for regno {regno:#x}!"),
            );
            abstract_read_reg_expect_err(&mut hart, regno, CMDERR_EXCEPTION)?;
        }

        log::info!(
            "Checking that only 64-bit reads from SCRs mtcc, mtdc, dscratch0, dscratch1 succeed"
        );
        for regno in [
            ABSTRACT_REGNO_SCR_MTCC,
            ABSTRACT_REGNO_SCR_MTDC,
            ABSTRACT_REGNO_SCR_DSCRATCH0,
            ABSTRACT_REGNO_SCR_DSCRATCH1,
        ] {
            let _ = abstract_read_cap(&mut hart, regno)?;
            abstract_read_reg_expect_err(&mut hart, regno, CMDERR_EXCEPTION)?;
        }

        log::info!("Testing read from CSRs mtval");
        ensure!(
            abstract_read_reg(&mut hart, ABSTRACT_REGNO_CSR_MTVAL)? == mtval,
            format!("incorrect register value for regno {ABSTRACT_REGNO_CSR_MTVAL:#x}!")
        );
        abstract_read_cap_expect_err(&mut hart, ABSTRACT_REGNO_CSR_MTVAL, CMDERR_NOT_SUPPORTED)?;

        log::info!("Testing reads from CSRs mscratch, dscratch0, dscratch1");
        for regno in [
            ABSTRACT_REGNO_CSR_MSCRATCH,
            ABSTRACT_REGNO_CSR_DSCRATCH0,
            ABSTRACT_REGNO_CSR_DSCRATCH1,
        ] {
            let _ = abstract_read_reg(&mut hart, regno)?;
        }

        log::info!(
            "Checking that 32-bit and 64-bit reads from GPRs x16-x31 in CHERIoT causes exceptions"
        );
        for regno in ABSTRACT_REGNO_GPR_LAST_CHERIOT + 1..=ABSTRACT_REGNO_GPR_LAST {
            abstract_read_reg_expect_err(&mut hart, regno, CMDERR_EXCEPTION)?;
            abstract_read_cap_expect_err(&mut hart, regno, CMDERR_EXCEPTION)?;
        }

        resume(&mut hart, ABSTRACT_REGNO_GPR_FIRST + 1)?;
    }

    UartConsole::wait_for(uart, r"READY", opts.timeout)?;
    {
        halt(&mut hart)?;

        log::info!("checking that capability tags are cleared on 32-bit writes");

        let regno_scratch = 10;
        for reg in 1..8 {
            abstract_write_reg(&mut hart, ABSTRACT_REGNO_GPR_FIRST + regno_scratch, 0)?;

            let regno = ABSTRACT_REGNO_GPR_FIRST + reg;

            hart.progbuf_execute(&[inst_cgettag(regno_scratch, reg)?])?;

            let tag = abstract_read_reg(&mut hart, ABSTRACT_REGNO_GPR_FIRST + regno_scratch)?;
            ensure!(tag == 1, "tag is unexpectedly unset");

            let value = abstract_read_reg(&mut hart, regno)?;
            abstract_write_reg(&mut hart, regno, value)?;

            hart.progbuf_execute(&[inst_cgettag(regno_scratch, reg)?])?;

            let tag = abstract_read_reg(&mut hart, ABSTRACT_REGNO_GPR_FIRST + regno_scratch)?;
            ensure!(tag == 0, "tag is unexpectedly set");
        }

        resume(&mut hart, ABSTRACT_REGNO_GPR_FIRST + 8)?;
    }

    UartConsole::wait_for(uart, r"READY", opts.timeout)?;
    {
        halt(&mut hart)?;

        log::info!("checking that capability tags are cleared on 64-bit writes");

        let regno_scratch = 10;
        for reg in 1..8 {
            abstract_write_reg(&mut hart, ABSTRACT_REGNO_GPR_FIRST + regno_scratch, 0)?;

            let regno = ABSTRACT_REGNO_GPR_FIRST + reg;

            hart.progbuf_execute(&[inst_cgettag(regno_scratch, reg)?])?;

            let tag = abstract_read_reg(&mut hart, ABSTRACT_REGNO_GPR_FIRST + regno_scratch)?;
            ensure!(tag == 1, "tag is unexpectedly unset");

            let cap = abstract_read_cap(&mut hart, regno)?;
            abstract_write_cap(&mut hart, regno, cap)?;

            hart.progbuf_execute(&[inst_cgettag(regno_scratch, reg)?])?;

            let tag = abstract_read_reg(&mut hart, ABSTRACT_REGNO_GPR_FIRST + regno_scratch)?;
            ensure!(tag == 0, "tag is unexpectedly set");
        }

        resume(&mut hart, ABSTRACT_REGNO_GPR_FIRST + 8)?;
    }

    Ok(())
}

fn main() -> Result<()> {
    let opts = Opts::parse();
    opts.init.init_logging();
    let transport = opts.init.init_target()?;

    execute_test!(test_rv_dm_mode_switch, &opts, &transport);

    Ok(())
}
