// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#![allow(clippy::bool_assert_comparison)]
use anyhow::{Context, Result, anyhow};
use base64ct::{Base64, Decoder};
use clap::{Args, Parser, Subcommand, ValueEnum};

use std::io::Cursor;
use std::path::{Path, PathBuf};
use std::time::Duration;

use opentitanlib::app::TransportWrapper;
use opentitanlib::chip::boot_log::OwnershipState;
use opentitanlib::chip::boot_svc::{BootSlot, OwnershipActivateRequest, OwnershipUnlockRequest};
use opentitanlib::chip::device_id::DeviceId;
use opentitanlib::image::image::{self};
use opentitanlib::io::uart::Uart;
use opentitanlib::ownership::{
    CommandTag, OwnerBlock, OwnerConfigItem, OwnerRescueConfig, TlvHeader,
};
use opentitanlib::rescue::{EntryMode, RescueMode, RescueParams, RescueProtocol};
use opentitanlib::test_utils::init::InitializeTest;
use opentitanlib::transport::Capability;
use opentitanlib::uart::console::UartConsole;
use opentitanlib::util::file::FromReader;

#[derive(Debug, Parser)]
struct Opts {
    #[command(flatten)]
    init: InitializeTest,

    #[command(subcommand)]
    command: Commands,

    // Device ID represented as a hexadecimal string.
    // This format should correspond to how the ID is structured or stored
    // in the device's OTP.
    #[arg(long)]
    device_id: Option<String>,

    // Path to the owner block file. If not provided, it will be read from
    // the device's UART console.
    #[arg(long)]
    owner_block: Option<PathBuf>,

    /// Console receive timeout.
    #[arg(long, value_parser = humantime::parse_duration, default_value = "10s")]
    timeout: Duration,
}

#[derive(Clone, Debug, Args)]
struct RescueCommand {
    #[command(flatten)]
    params: RescueParams,

    #[arg(long)]
    action: RescueTestActions,
}

#[derive(Debug, Subcommand)]
enum Commands {
    Rescue(RescueCommand),
}

#[derive(ValueEnum, Debug, Clone, Copy, PartialEq)]
pub enum RescueTestActions {
    GetDeviceId,
    GetBootLog,
    GetOwnerPage,
    Disability,
}

fn get_device_id_test(
    expected_device_id_hex: &String,
    params: &RescueParams,
    transport: &TransportWrapper,
) -> Result<()> {
    let rescue = params.create(transport)?;
    rescue.enter(transport, EntryMode::Reset)?;
    let actual_device_id_from_rescue = rescue.get_device_id()?;
    let mut bytes_from_hex = hex::decode(expected_device_id_hex).map_err(|e| {
        anyhow!(
            "Failed to decode hex string '{}': {}",
            expected_device_id_hex,
            e
        )
    })?;
    // This reversal is to swap the byte order of the entire decoded hex sequence
    // to match the endianness expectation of the DeviceId::read function.
    bytes_from_hex.reverse();
    let mut cursor = Cursor::new(bytes_from_hex);
    let parsed_expected_device_id = DeviceId::read(&mut cursor).unwrap();
    if parsed_expected_device_id == actual_device_id_from_rescue {
        Ok(())
    } else {
        Err(anyhow!(
            "Device ID mismatch. Expected: {:?}, but got: {:?}",
            parsed_expected_device_id,
            actual_device_id_from_rescue
        ))
    }
}

fn get_boot_log_test(
    binary: &Path,
    params: &RescueParams,
    transport: &TransportWrapper,
) -> Result<()> {
    const BOOT_LOG_IDENTIFIER: u32 = u32::from_le_bytes(*b"BLOG");
    let image = image::Image::read_from_file(binary)?;
    let rescue = params.create(transport)?;
    rescue.enter(transport, EntryMode::Reset)?;
    let boot_log = rescue
        .get_boot_log()
        .context("Failed to get boot log from rescue")?;
    let rom_ext_manifest = image
        .subimages()?
        .first()
        .ok_or_else(|| anyhow!("No subimages found in the image"))?
        .manifest;
    if boot_log.rom_ext_major != rom_ext_manifest.version_major {
        return Err(anyhow!(
            "rom_ext_major mismatch. Expected: {}, but got: {}",
            rom_ext_manifest.version_major,
            boot_log.rom_ext_major
        ));
    }

    if boot_log.rom_ext_minor != rom_ext_manifest.version_minor {
        return Err(anyhow!(
            "rom_ext_minor mismatch. Expected: {}, but got: {}",
            rom_ext_manifest.version_minor,
            boot_log.rom_ext_minor
        ));
    }

    if boot_log.ownership_state != OwnershipState::LockedOwner {
        return Err(anyhow!(
            "ownership_state mismatch. Expected: {}, but got: {}",
            OwnershipState::LockedOwner,
            boot_log.ownership_state
        ));
    }

    if boot_log.identifier != BOOT_LOG_IDENTIFIER {
        return Err(anyhow!(
            "identifier mismatch. Expected: {}, but got: {}",
            BOOT_LOG_IDENTIFIER,
            boot_log.identifier
        ));
    }

    if boot_log.rom_ext_slot != BootSlot::SlotA {
        return Err(anyhow!(
            "rom_ext_slot mismatch. Expected: {}, but got: {}",
            BootSlot::SlotA,
            boot_log.rom_ext_slot
        ));
    }

    Ok(())
}

fn get_owner_page_test(
    owner_block: &OwnerBlock,
    params: &RescueParams,
    transport: &TransportWrapper,
) -> Result<()> {
    let rescue = params.create(transport)?;
    rescue.enter(transport, EntryMode::Reset)?;
    let data = rescue
        .get_raw(RescueMode::GetOwnerPage0)
        .context("Failed to get owner page from rescue")?;

    let mut cursor = std::io::Cursor::new(&data);
    let header = TlvHeader::read(&mut cursor)?;
    let owner_block_from_rescue = OwnerBlock::read(&mut cursor, header)?;

    if *owner_block == owner_block_from_rescue {
        Ok(())
    } else {
        Err(anyhow!(
            "Owner Page mismatch. Expected: {:?}, but got: {:?}",
            owner_block,
            owner_block_from_rescue
        ))
    }
}

fn load_owner_block(
    owner_block: Option<&Path>,
    transport: &TransportWrapper,
) -> Result<OwnerBlock> {
    let mut input = Vec::new();

    match owner_block {
        None => {
            let uart = transport.uart("console")?;
            let capture = UartConsole::wait_for(
                &*uart,
                r"(?msR)OWNER_PAGE_0: (.*?)\r\n",
                Duration::from_secs(1),
            )?;
            if capture.len() < 2 {
                return Err(anyhow!(
                    "OWNER_PAGE_0 base64 data not captured from console"
                ));
            }
            let owner_page_0_base64_str = &capture[1];
            if owner_page_0_base64_str.is_empty() {
                return Err(anyhow!("OWNER_PAGE_0 base64 string is empty"));
            }
            let mut decoder = Decoder::<Base64>::new(owner_page_0_base64_str.as_bytes())?;
            decoder.decode_to_end(&mut input)?;
        }
        Some(block) => {
            input = std::fs::read(block)?;
        }
    }
    let mut cursor = std::io::Cursor::new(&input);
    let header = TlvHeader::read(&mut cursor)?;
    let owner_block_obj = OwnerBlock::read(&mut cursor, header)?;
    Ok(owner_block_obj)
}

fn expect_err_from_rescue_result<T, E>(result: Result<T, E>, error: &str) -> Result<()>
where
    E: std::fmt::Display,
{
    match result {
        Ok(_) => Err(anyhow!("Sending a disallowed command should fail")),
        Err(e) => {
            if e.to_string().contains(error) {
                Ok(())
            } else {
                Err(anyhow!("Unexpected error: {}", e.to_string()))
            }
        }
    }
}

fn expect_err<T, E>(
    result: Result<T, E>,
    error: &str,
    uart_console: Option<&dyn Uart>,
) -> Result<()>
where
    E: std::fmt::Display,
{
    match uart_console {
        // If no UART console is provided (implying XMODEM variant), check the rescue operation result directly.
        None => expect_err_from_rescue_result(result, error),

        // With a UART console (for DFU), we primarily check the device log for the expected error because the
        // rescue operation result might not report the disallowed error properly in some rescue configurations.
        Some(console) => {
            if error.is_empty() {
                // SPECIAL CASE: An empty 'error' string signals a specific scenario
                // (e.g., BootSvcReq allowed, but its sub-commands are disallowed).
                // In this situation, there is no informative device log.
                // The rescue operation result is checked for an error message containing "Vendor".
                expect_err_from_rescue_result(result, "Vendor")
            } else {
                // The pattern may have multiple lines, so we need to wait for them one at a time.
                for line in error.split("\r\n") {
                    log::info!("wait for {line:?}");
                    let _ = UartConsole::wait_for(console, line, Duration::from_secs(1))?;
                }
                Ok(())
            }
        }
    }
}

macro_rules! expect_disallowed_cmd {
    ($uart_console:expr, $command_allow_list:expr, $command_tag:expr, $operation:expr, $reset:expr, $expected_err_str:expr $(,)?) => {
        if !$command_allow_list.contains(&$command_tag) {
            log::info!("Testing disallowed command: {}", $command_tag,);
            expect_err($operation, $expected_err_str, $uart_console)?;
            ($reset)?;
        }
    };
}

fn get_expected_err_msg(command: CommandTag, params: &RescueParams) -> String {
    let command_string = String::from_utf8(command.0.to_be_bytes().to_vec()).unwrap_or_default();
    match params.protocol {
        RescueProtocol::Xmodem => format!(r"bad mode: mode: {}", &command_string),
        _ => format!("mode: {}\r\nerror: mode not allowed", &command_string),
    }
}

fn disability_test(
    owner_block: &mut OwnerBlock,
    params: &RescueParams,
    transport: &TransportWrapper,
) -> Result<()> {
    let rescue_config: Option<&mut OwnerRescueConfig> =
        owner_block.data.iter_mut().find_map(|item| {
            if let OwnerConfigItem::RescueConfig(config) = item {
                Some(config)
            } else {
                None
            }
        });

    match rescue_config {
        None => {
            println!("No RescueConfig found. All the rescue commands are allowed by default");
            Ok(())
        }
        Some(config) => {
            let rescue = params.create(transport)?;
            rescue.enter(transport, EntryMode::Reset)?;

            let uart_console = if params.protocol == RescueProtocol::Xmodem {
                None
            } else {
                transport.capabilities()?.request(Capability::UART).ok()?;
                Some(
                    transport
                        .uart("console")
                        .expect("Failed to init Uart console"),
                )
            };

            let boot_svc_req_allowed = config.command_allow.contains(&CommandTag::BootSvcReq);

            if !boot_svc_req_allowed {
                // If `BootSvcReq` is disallowed, it implicitly disallows the following
                // boot services commands, even if they are individually specified in the allow list.
                let targets_to_remove = [
                    CommandTag::Empty,
                    CommandTag::MinBl0SecVerRequest,
                    CommandTag::NextBl0SlotRequest,
                    CommandTag::OwnershipActivateRequest,
                    CommandTag::OwnershipUnlockRequest,
                ];
                config
                    .command_allow
                    .retain(|cmd| !targets_to_remove.contains(cmd));
            }

            const DUMMY_BYTES: [u8; 256] = [0u8; 256];
            expect_disallowed_cmd!(
                uart_console.as_deref(),
                config.command_allow,
                CommandTag::Rescue,
                rescue.update_firmware(BootSlot::SlotA, &DUMMY_BYTES),
                rescue.enter(transport, EntryMode::Reset),
                &get_expected_err_msg(CommandTag::Rescue, params)
            );

            expect_disallowed_cmd!(
                uart_console.as_deref(),
                config.command_allow,
                CommandTag::RescueB,
                rescue.update_firmware(BootSlot::SlotB, &DUMMY_BYTES),
                rescue.enter(transport, EntryMode::Reset),
                &get_expected_err_msg(CommandTag::RescueB, params)
            );

            expect_disallowed_cmd!(
                uart_console.as_deref(),
                config.command_allow,
                CommandTag::GetDeviceId,
                rescue.get_device_id(),
                rescue.enter(transport, EntryMode::Reset),
                &get_expected_err_msg(CommandTag::GetDeviceId, params)
            );

            expect_disallowed_cmd!(
                uart_console.as_deref(),
                config.command_allow,
                CommandTag::GetBootLog,
                rescue.get_boot_log(),
                rescue.enter(transport, EntryMode::Reset),
                &get_expected_err_msg(CommandTag::GetBootLog, params)
            );

            expect_disallowed_cmd!(
                uart_console.as_deref(),
                config.command_allow,
                CommandTag::GetOwnerPage0,
                rescue.get_raw(RescueMode::GetOwnerPage0),
                rescue.enter(transport, EntryMode::Reset),
                &get_expected_err_msg(CommandTag::GetOwnerPage0, params)
            );

            // GetOwnerPage1 command is only supported in Xmodem variant.
            if params.protocol == RescueProtocol::Xmodem {
                expect_disallowed_cmd!(
                    uart_console.as_deref(),
                    config.command_allow,
                    CommandTag::GetOwnerPage1,
                    rescue.get_raw(RescueMode::GetOwnerPage1),
                    rescue.enter(transport, EntryMode::Reset),
                    &get_expected_err_msg(CommandTag::GetOwnerPage1, params)
                );
            }

            // When BootSvcReq is allowed but its sub-commands are not:
            // - XMODEM propagates the rescue error as "Cancelled".
            // - DFU won't have a device log error; an empty string is used.
            //  This is a signal for `expect_err` to use fallback logic.
            let boot_svc_req_sub_cmd_err_msg = if boot_svc_req_allowed {
                if params.protocol == RescueProtocol::Xmodem {
                    "Cancelled".to_string()
                } else {
                    "".to_string()
                }
            } else {
                get_expected_err_msg(CommandTag::BootSvcReq, params)
            };

            const DUMMY_PAYLOAD: [u32; 64] = [0u32; 64];
            expect_disallowed_cmd!(
                uart_console.as_deref(),
                config.command_allow,
                CommandTag::Empty,
                rescue.empty(DUMMY_PAYLOAD.as_ref()),
                rescue.enter(transport, EntryMode::Reset),
                &boot_svc_req_sub_cmd_err_msg,
            );

            const NEW_BL0_VER: u32 = 2;
            expect_disallowed_cmd!(
                uart_console.as_deref(),
                config.command_allow,
                CommandTag::MinBl0SecVerRequest,
                rescue.set_min_bl0_sec_ver(NEW_BL0_VER),
                rescue.enter(transport, EntryMode::Reset),
                &boot_svc_req_sub_cmd_err_msg,
            );

            expect_disallowed_cmd!(
                uart_console.as_deref(),
                config.command_allow,
                CommandTag::NextBl0SlotRequest,
                rescue.set_next_bl0_slot(BootSlot::SlotA, BootSlot::SlotA),
                rescue.enter(transport, EntryMode::Reset),
                &boot_svc_req_sub_cmd_err_msg,
            );

            expect_disallowed_cmd!(
                uart_console.as_deref(),
                config.command_allow,
                CommandTag::OwnershipUnlockRequest,
                rescue.ownership_unlock(OwnershipUnlockRequest::default()),
                rescue.enter(transport, EntryMode::Reset),
                &boot_svc_req_sub_cmd_err_msg,
            );

            expect_disallowed_cmd!(
                uart_console.as_deref(),
                config.command_allow,
                CommandTag::OwnershipActivateRequest,
                rescue.ownership_activate(OwnershipActivateRequest::default()),
                rescue.enter(transport, EntryMode::Reset),
                &boot_svc_req_sub_cmd_err_msg,
            );

            expect_disallowed_cmd!(
                uart_console.as_deref(),
                config.command_allow,
                CommandTag::BootSvcRsp,
                rescue.get_boot_svc(),
                rescue.enter(transport, EntryMode::Reset),
                &get_expected_err_msg(CommandTag::BootSvcRsp, params)
            );

            Ok(())
        }
    }
}

fn main() -> Result<()> {
    let opts = Opts::parse();
    opts.init.init_logging();
    let transport = opts.init.init_target()?;

    match opts.command {
        Commands::Rescue(rescue) => match rescue.action {
            RescueTestActions::GetDeviceId => {
                let device_id = &opts
                    .device_id
                    .as_ref()
                    .ok_or_else(|| anyhow!("No device_id provided"))?;
                get_device_id_test(device_id, &rescue.params, &transport)?;
            }
            RescueTestActions::GetBootLog => {
                let binary = &opts
                    .init
                    .bootstrap
                    .bootstrap
                    .as_ref()
                    .ok_or_else(|| anyhow!("No RV32 test binary provided"))?;
                get_boot_log_test(binary, &rescue.params, &transport)?;
            }
            RescueTestActions::GetOwnerPage => {
                let owner_block = load_owner_block(opts.owner_block.as_deref(), &transport)?;
                get_owner_page_test(&owner_block, &rescue.params, &transport)?;
            }
            RescueTestActions::Disability => {
                let mut owner_block = load_owner_block(opts.owner_block.as_deref(), &transport)?;
                disability_test(&mut owner_block, &rescue.params, &transport)?;
            }
        },
    }
    Ok(())
}
