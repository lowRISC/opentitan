// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::{bail, Result};
use opentitanlib::dif::rstmgr::DifRstmgrResetInfo;
use opentitanlib::transport::common::fpga::ClearBitstream;
use regex::Regex;
use std::fs::File;
use std::io::Write;
use std::process::{Command, Stdio};
use std::time::Duration;
use structopt::StructOpt;

use opentitanlib::app::TransportWrapper;
use opentitanlib::chip::boolean::MultiBitBool8;
use opentitanlib::dif::lc_ctrl::{
    DifLcCtrlState, DifLcCtrlToken, LcBit, LcCtrlReg, LcCtrlStatusBit, LcCtrlTransitionCmdBit,
    LcCtrlTransitionRegwenBit,
};
use opentitanlib::execute_test;
use opentitanlib::test_utils::init::InitializeTest;
use opentitanlib::uart::console::{ExitStatus, UartConsole};

const CONSOLE_TIMEOUT: Duration = Duration::from_secs(5);
const JTAG_TAP_NAME: &str = "lc_ctrl.tap.0";

#[derive(Debug, StructOpt)]
struct Opts {
    #[structopt(flatten)]
    init: InitializeTest,

    #[structopt(long, help = "Path to OpenOCD binary")]
    openocd: String,

    #[structopt(long, help = "Path to OpenOCD JTAG adapter config")]
    openocd_adapter_config: String,
}

// RAII-style struct that clears the FPGA's bitstream when it goes out of scope.
struct ScopedBitstream<'a> {
    transport: &'a TransportWrapper,
}

impl Drop for ScopedBitstream<'_> {
    fn drop(&mut self) {
        self.transport
            .dispatch(&ClearBitstream {})
            .expect("Should dispatch ClearBitstream command successfully");
    }
}

/// A domain-specific language for reading and writing lifecycle controller
/// registers. It compiles to TCL that OpenOCD can interpret. The goal is to
/// provide a notation for our tests rather than map one-to-one with TCL syntax
/// or OpenOCD primitives.
#[derive(Debug)]
enum OpenocdTclBlock<'a> {
    /// Exits OpenOCD with a non-zero status when the register does not contain
    /// the given value.
    AssertRegEq(LcCtrlReg, u32),

    /// Polls the register a finite number of times until its value matches the
    /// expectation. Exits OpenOCD with a non-zero status if it runs out of
    /// tries.
    PollUntilRegEq(LcCtrlReg, u32),

    /// Writes the given value to the register.
    WriteReg(LcCtrlReg, u32),

    /// Echoes the given string to stdout. The string must be trivially
    /// quotable, so it must not contain double quotes, backslashes, etc.
    Echo(&'a str),
}

impl OpenocdTclBlock<'_> {
    /// Compiles this operation to a JimTCL string that OpenOCD can execute.
    fn to_tcl(self) -> String {
        match self {
            // Contrary to OpenOCD's documentation [0], I can't get `shutdown
            // [error]` to affect OpenOCD's exit code.  My hacky workaround is
            // to create my own fatal error by using a nonexistent command.
            //
            // [0]: https://openocd.org/doc/html/General-Commands.html
            OpenocdTclBlock::AssertRegEq(register, expectation) => {
                let reg_offset = register.word_offset();
                format!(
                    r#"
set reg_value [ {JTAG_TAP_NAME} riscv dmi_read 0x{reg_offset:x} ]
if {{ $reg_value != {expectation} }} {{
    echo "Expected {register:?} == 0x{expectation:x}, but it is $reg_value"
    nonexistent_command_that_causes_openocd_to_exit_with_error
}}"#
                )
            }
            OpenocdTclBlock::PollUntilRegEq(register, expectation) => {
                const MAX_ATTEMPTS: u32 = 1000;
                const SLEEP_MILLIS: u32 = 5;
                let reg_offset = register.word_offset();
                format!(
                    r#"
for {{ set i 0 }} {{ $i < {MAX_ATTEMPTS} }} {{ set i [expr {{$i + 1}}] }} {{
    set reg_value [ {JTAG_TAP_NAME} riscv dmi_read 0x{reg_offset:x} ]
    if {{ $reg_value == {expectation} }} {{
        break
    }}
    sleep {SLEEP_MILLIS}
}}
if {{ $i == {MAX_ATTEMPTS} }} {{
    echo "Ran out of attempts before {register:?} became 0x{expectation:x}"
    nonexistent_command_that_causes_openocd_to_exit_with_error
}}"#
                )
            }
            OpenocdTclBlock::WriteReg(register, value) => {
                let reg_offset = register.word_offset();
                format!("{JTAG_TAP_NAME} riscv dmi_write 0x{reg_offset:x} 0x{value:x}")
            }
            OpenocdTclBlock::Echo(s) => {
                // Do the bare minimum validation before we naively quote `s`.
                assert!(!s.chars().any(|c| ['\n', '\r', '"', '\\'].contains(&c)));
                format!("echo \"{s}\"")
            }
        }
    }
}

/// Resets the device with the given strappings applied. Clears the UART RX
/// buffer. Removes the strappings before returning.
fn reset(transport: &TransportWrapper, strappings: &[&str], reset_delay: Duration) -> Result<()> {
    log::info!("Resetting target...");
    for strapping in strappings.iter() {
        transport.apply_pin_strapping(strapping)?;
    }
    transport.reset_target(reset_delay, true)?;
    for strapping in strappings.iter() {
        transport.remove_pin_strapping(strapping)?;
    }
    Ok(())
}

/// Orchestrates iteration 2 of the rom_bootstrap_rma testpoint. Issue the life
/// cycle RMA command and ensure the RMA transition is completed successfully.
fn test_rma_command(opts: &Opts, transport: &TransportWrapper) -> Result<()> {
    use LcCtrlReg::{
        ClaimTransitionIf, LcState, LcTransitionCnt, Status, TransitionCmd, TransitionRegwen,
        TransitionTarget, TransitionToken0, TransitionToken1, TransitionToken2, TransitionToken3,
    };
    use OpenocdTclBlock::{AssertRegEq, Echo, PollUntilRegEq, WriteReg};

    // This is the preimage of the RMA token. The postimage is already stored in
    // the OTP's SECRET2 partition.
    let token = DifLcCtrlToken::from([
        0x53, 0xa3, 0x81, 0x2b, 0x5a, 0x4c, 0x04, 0xa4, //
        0x85, 0xda, 0xac, 0x25, 0x2d, 0x14, 0x5c, 0xaf,
    ]);
    let [token0, token1, token2, token3] = token.into_register_values();

    let script_transition_to_rma = [
        Echo("--- Waiting for controller to be ready..."),
        PollUntilRegEq(
            Status,
            LcBit::union([LcCtrlStatusBit::Initialized, LcCtrlStatusBit::Ready]),
        ),
        Echo("--- Lifecycle controller is ready!"),
        AssertRegEq(LcState, DifLcCtrlState::Prod.redundant_encoding()),
        AssertRegEq(LcTransitionCnt, 5),
        WriteReg(ClaimTransitionIf, u8::from(MultiBitBool8::True).into()),
        AssertRegEq(ClaimTransitionIf, u8::from(MultiBitBool8::True).into()),
        AssertRegEq(
            TransitionRegwen,
            LcBit::union([LcCtrlTransitionRegwenBit::TransitionRegwen]),
        ),
        WriteReg(TransitionToken0, token0),
        WriteReg(TransitionToken1, token1),
        WriteReg(TransitionToken2, token2),
        WriteReg(TransitionToken3, token3),
        AssertRegEq(TransitionToken0, token0),
        AssertRegEq(TransitionToken1, token1),
        AssertRegEq(TransitionToken2, token2),
        AssertRegEq(TransitionToken3, token3),
        WriteReg(TransitionTarget, DifLcCtrlState::Rma.redundant_encoding()),
        AssertRegEq(TransitionTarget, DifLcCtrlState::Rma.redundant_encoding()),
        Echo("--- Initiate the life cycle transition"),
        WriteReg(TransitionCmd, LcBit::union([LcCtrlTransitionCmdBit::Start])),
        AssertRegEq(TransitionRegwen, 0),
        AssertRegEq(Status, LcBit::union([LcCtrlStatusBit::Initialized])),
        Echo("--- Poll the STATUS register while device erases flash..."),
        PollUntilRegEq(
            Status,
            LcBit::union([
                LcCtrlStatusBit::Initialized,
                LcCtrlStatusBit::TransitionSuccessful,
            ]),
        ),
        AssertRegEq(LcState, DifLcCtrlState::PostTransition.redundant_encoding()),
        Echo("--- Lifecycle transition complete"),
    ];

    let script_contents: String = script_transition_to_rma
        .map(OpenocdTclBlock::to_tcl)
        .join("\n");

    const SCRIPT_FILE_PATH: &str = "tmp_script.cfg";
    File::create(SCRIPT_FILE_PATH)?.write_all(script_contents.as_bytes())?;

    // In subsequent runs of this test, OpenOCD will fail with the following
    // error unless we preemptively clear the bitstream.
    // ```
    //     Error: dmi_read is not implemented for this target.
    //
    //     Error: Unsupported DTM version: 15
    //     Finished test test_rma_command: Err(OpenOCD exited with code 1
    // ```
    //
    // There's another failure mode: after starting the transition, sometimes
    // OpenOCD will complain that the DMI operation timed out. Retrying the test
    // never resolves it, but clearing the FPGA bitstream *sometimes* resolves
    // it.
    // ```
    //     Error: DMI operation didn't complete in 2 seconds. The target is
    //     either really slow or broken. You could increase the timeout with
    //     riscv set_command_timeout_sec.
    // ```
    //
    // To minimize flakiness, clear the bitstream before leaving this function.
    let _scoped_bitstream = ScopedBitstream { transport };

    reset(
        transport,
        &["RMA_BOOTSTRAP", "PINMUX_TAP_LC"],
        opts.init.bootstrap.options.reset_delay,
    )?;

    let openocd_exit = Command::new(&opts.openocd)
        .args(["-f", &opts.openocd_adapter_config])
        .args(["-c", "adapter speed 200;"])
        // Tell OpenOCD how to connect to the lifecycle controller's RISC-V TAP.
        // This works because lc_ctrl uses an instance of the RISC-V debug
        // module [0]. Its IRLEN is hardcoded to 5 [1] and its IDCODE is 1 [2].
        //
        // [0]: https://docs.opentitan.org/hw/ip/lc_ctrl/doc/#life-cycle-tap-controller
        // [1]: See where `dmi_jtag_tap` is created in hw/vendor/pulp_riscv_dbg/src/dmi_jtag.sv
        // [2]: See where `dmi_jtag` is instantiated in hw/ip/lc_ctrl/rtl/lc_ctrl.sv
        //
        // Because these commands are command-line args, they *must* end with
        // semicolons to satisfy the TCL lexer. When a TCL program is read from
        // a file, newlines are sufficient to separate statements.
        .args([
            "-c",
            "transport select jtag;",
            "-c",
            "jtag newtap lc_ctrl tap -irlen 5 -expected-id 0x00000001 -ignore-bypass;",
            "-c",
            &format!(
                "target create {JTAG_TAP_NAME} riscv -chain-position lc_ctrl.tap -rtos hwthread;"
            ),
            "-c",
            "init;",
        ])
        .args(["-f", SCRIPT_FILE_PATH])
        .args(["-c", "shutdown;"])
        .stdout(Stdio::inherit())
        .stderr(Stdio::inherit())
        .spawn()?
        .wait()?;

    if !openocd_exit.success() {
        bail!("OpenOCD exited with status {}", openocd_exit);
    }

    // Reset the device and confirm that its lifecycle state is now RMA by
    // reading the "LCV:" line from the UART.
    let uart = transport.uart("console")?;
    reset(transport, &[], opts.init.bootstrap.options.reset_delay)?;
    let mut console = UartConsole {
        timeout: Some(CONSOLE_TIMEOUT),
        exit_success: Some(Regex::new(&format!(
            "LCV:{:x}\r\n",
            DifLcCtrlState::Rma.redundant_encoding()
        ))?),
        exit_failure: Some(Regex::new(r"LCV:[0-9a-f]+\r\n")?),
        ..Default::default()
    };
    let result = console.interact(&*uart, None, Some(&mut std::io::stdout()))?;
    if result != ExitStatus::ExitSuccess {
        bail!("FAIL: {:?}", result);
    };
    Ok(())
}

/// Orchestrates iteration 1 of the rom_bootstrap_rma testpoint. This never
/// issues the life cycle RMA command. It verifies that the ROM times out on
/// spin cycles, automatically resets the device, and logs the expected reset
/// reasons.
fn test_no_rma_command(opts: &Opts, transport: &TransportWrapper) -> Result<()> {
    let uart = transport.uart("console")?;
    reset(
        transport,
        &["RMA_BOOTSTRAP"],
        opts.init.bootstrap.options.reset_delay,
    )?;

    log::info!("Waiting for reset reasons on console...");

    // The `exit_success` and `exit_failure` patterns are tightly coupled with
    // sw/device/silicon_creator/rom/e2e/rom_e2e_bootstrap_rma_test.c.
    let expected_bitfield = u32::from(DifRstmgrResetInfo::Por) | u32::from(DifRstmgrResetInfo::Sw);
    let mut console = UartConsole {
        timeout: Some(CONSOLE_TIMEOUT),
        exit_success: Some(Regex::new(&format!(
            "reset_info_bitfield: 0x{expected_bitfield:x}\r\n"
        ))?),
        exit_failure: Some(Regex::new(r"reset_info_bitfield: 0x[0-9a-f]+\r\n")?),
        ..Default::default()
    };
    let result = console.interact(&*uart, None, Some(&mut std::io::stdout()))?;
    if result != ExitStatus::ExitSuccess {
        bail!("FAIL: {:?}", result);
    };
    Ok(())
}

fn main() -> Result<()> {
    let opts = Opts::from_args();
    opts.init.init_logging();
    let transport = opts.init.init_target()?;
    execute_test!(test_no_rma_command, &opts, &transport);
    execute_test!(test_rma_command, &opts, &transport);
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn openocd_statements() {
        assert_eq!(
            OpenocdTclBlock::AssertRegEq(LcCtrlReg::LcIdState, 0x3c).to_tcl(),
            r#"
set reg_value [ lc_ctrl.tap.0 riscv dmi_read 0xf ]
if { $reg_value != 60 } {
    echo "Expected LcIdState == 0x3c, but it is $reg_value"
    nonexistent_command_that_causes_openocd_to_exit_with_error
}"#
        );

        assert_eq!(
            OpenocdTclBlock::PollUntilRegEq(LcCtrlReg::TransitionToken0, 0x1234).to_tcl(),
            r#"
for { set i 0 } { $i < 1000 } { set i [expr {$i + 1}] } {
    set reg_value [ lc_ctrl.tap.0 riscv dmi_read 0x6 ]
    if { $reg_value == 4660 } {
        break
    }
    sleep 5
}
if { $i == 1000 } {
    echo "Ran out of attempts before TransitionToken0 became 0x1234"
    nonexistent_command_that_causes_openocd_to_exit_with_error
}"#
        );
        assert_eq!(
            OpenocdTclBlock::WriteReg(LcCtrlReg::TransitionToken3, 0xabcd).to_tcl(),
            "lc_ctrl.tap.0 riscv dmi_write 0x9 0xabcd"
        );

        assert_eq!(OpenocdTclBlock::Echo("bar").to_tcl(), "echo \"bar\"");
    }

    /// Stringifying echo statements should panic when they contain unsupported
    /// characters.
    #[test]
    #[should_panic]
    fn openocd_statements_echo_panic() {
        let _s = OpenocdTclBlock::Echo("bad string \"").to_tcl();
    }
}
