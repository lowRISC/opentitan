// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#![allow(clippy::bool_assert_comparison)]
use anyhow::{Result, anyhow};
use clap::{Args, Parser, Subcommand, ValueEnum};

use std::time::Duration;

use opentitanlib::app::TransportWrapper;
use opentitanlib::io::eeprom::{AddressMode, MODE_111, Transaction};
use opentitanlib::io::spi::SpiParams;
use opentitanlib::rescue::dfu::{DfuOperations, DfuRequestType};
use opentitanlib::rescue::{EntryMode, Rescue, RescueMode, RescueParams, SpiDfu, UsbDfu};
use opentitanlib::spiflash::SpiFlash;
use opentitanlib::test_utils::init::InitializeTest;
use opentitanlib::uart::console::UartConsole;

#[derive(Debug, Parser)]
struct Opts {
    #[command(flatten)]
    init: InitializeTest,

    /// Console receive timeout.
    #[arg(long, value_parser = humantime::parse_duration, default_value = "10s")]
    timeout: Duration,

    #[command(subcommand)]
    command: Commands,
}

#[derive(Clone, Debug, Args)]
pub struct RescueCommand {
    #[command(flatten)]
    params: RescueParams,

    #[arg(long)]
    action: DfuRescueTestActions,
}

#[derive(Debug, Subcommand)]
enum Commands {
    Rescue(RescueCommand),
}

#[derive(ValueEnum, Debug, Clone, Copy, PartialEq)]
pub enum DfuRescueTestActions {
    SpiDfuStateTransitions,
    InvalidSpiDfuRequests,
    InvalidSpiFlashTransaction,
    UsbDfuOutChunkTooBig,
}

const SET_INTERFACE: u8 = 0x0b;
const INVALID_INTERFACE: u8 = 0xff;

const DFU_REQUEST_TYPE_INTERFACE: u8 = 0x01;

const DFU_REQ_DN_LOAD: u8 = 0x01;
const DFU_REQ_CLR_STATUS: u8 = 0x04;
const DFU_REQ_GET_STATE: u8 = 0x05;
const DFU_REQ_ABORT: u8 = 0x06;
const DFU_REQ_INVALID: u8 = 0xff;

const USB_SETUP_REQ_GET_INTERFACE: u8 = 0x0A;
const USB_SETUP_REQ_SET_INTERFACE: u8 = 0x0B;

fn expect_usb_bad_mode_write_control(
    rescue: &SpiDfu,
    request_type: u8,
    request: u8,
    value: u16,
    index: u16,
) -> Result<()> {
    let result = rescue.write_control(request_type, request, value, index, &[]);
    match result {
        Ok(_) => Err(anyhow!("Invalid write control should fail")),
        Err(e) => {
            if e.to_string().contains("UsbBadSetup") {
                Ok(())
            } else {
                Err(anyhow!("Unexpected error: {}", e.to_string()))
            }
        }
    }
}

fn expect_usb_bad_mode_read_control(
    rescue: &SpiDfu,
    request_type: u8,
    request: u8,
    value: u16,
    index: u16,
    data: &mut [u8],
) -> Result<()> {
    let result = rescue.read_control(request_type, request, value, index, data);
    match result {
        Ok(_) => Err(anyhow!("Invalid read control should fail")),
        Err(e) => {
            if e.to_string().contains("UsbBadSetup") {
                Ok(())
            } else {
                Err(anyhow!("Unexpected error: {}", e.to_string()))
            }
        }
    }
}

fn spi_dfu_state_transitions(params: &RescueParams, transport: &TransportWrapper) -> Result<()> {
    let spi_params = SpiParams::default();
    let spi = spi_params.create(transport, "BOOTSTRAP")?;
    let rescue = SpiDfu::new(spi.clone(), params.clone());
    rescue.enter(transport, EntryMode::Reset)?;

    let setting = u32::from(RescueMode::BootSvcRsp);
    rescue.write_control(
        DfuRequestType::Vendor.into(),
        SET_INTERFACE,
        (setting >> 16) as u16,
        setting as u16,
        &[],
    )?;

    // Test a `kDfuReqAbort` request. This should trigger the `kDfuActionNone`
    // action, causing a state transition from `kDfuStateIdle` to `kDfuStateIdle`.
    rescue.write_control(DfuRequestType::Out.into(), DFU_REQ_ABORT, 0, 0, &[])?;

    // Test a `kDfuReqGetState` request. This should trigger the
    // `kDfuActionStateResponse` action, causing a state transition from
    // `kDfuStateIdle` to `kDfuStateUpLoadIdle`.
    rescue.write_control(DfuRequestType::Out.into(), DFU_REQ_GET_STATE, 0, 0, &[])?;

    // Test a `kDfuReqClrStatus` request when not in the error state. This should
    // trigger the `kDfuActionStall` action, causing a state transition from
    // `kDfuStateUpLoadIdle` to `kDfuStateError`.
    expect_usb_bad_mode_write_control(
        &rescue,
        DfuRequestType::Out.into(),
        DFU_REQ_CLR_STATUS,
        0,
        0,
    )?;
    // Test a `kDfuReqClrStatus` request in the error state. This should trigger
    // the `kDfuActionClearError` action, causing a state transition from
    // `kDfuStateError` to `kDfuStateIdle`.
    rescue.write_control(DfuRequestType::Out.into(), DFU_REQ_CLR_STATUS, 0, 0, &[])?;

    // Test a `kDfuReqDnLoad` request with a payload larger than the DFU buffer.
    // This should cause a state transition from `kDfuStateIdle` to `kDfuStateError`.
    let mut payload_too_big = [0u8; 2050];
    expect_usb_bad_mode_read_control(
        &rescue,
        DfuRequestType::Out.into(),
        DFU_REQ_DN_LOAD,
        0,
        0,
        &mut payload_too_big,
    )?;

    // Clear the error state, transitioning from `kDfuStateError` to `kDfuStateIdle`.
    rescue.write_control(DfuRequestType::Out.into(), DFU_REQ_CLR_STATUS, 0, 0, &[])?;

    // Test a `kDfuReqDnLoad` request that would write past the end of flash.
    // This should cause a state transition from `kDfuStateIdle` to `kDfuStateError`.
    let mut payload = [0u8; 1];
    expect_usb_bad_mode_read_control(
        &rescue,
        DfuRequestType::Out.into(),
        DFU_REQ_DN_LOAD,
        0,
        0,
        &mut payload,
    )?;

    // Test an invalid DFU request.
    expect_usb_bad_mode_write_control(
        &rescue,
        DfuRequestType::Out.into(),
        DFU_REQ_INVALID,
        (setting >> 16) as u16,
        setting as u16,
    )?;

    rescue.reboot()?;

    let uart = transport.uart("console")?;
    UartConsole::wait_for(&*uart, r"Finished", Duration::from_secs(5))?;

    Ok(())
}

fn invalid_spi_dfu_requests(params: &RescueParams, transport: &TransportWrapper) -> Result<()> {
    let spi_params = SpiParams::default();
    let spi = spi_params.create(transport, "BOOTSTRAP")?;
    let rescue = SpiDfu::new(spi.clone(), params.clone());
    rescue.enter(transport, EntryMode::Reset)?;

    let setting = u32::from_be_bytes(*b"INVA");
    // Test an invalid rescue mode with a vendor SET_INTERFACE request.
    expect_usb_bad_mode_write_control(
        &rescue,
        DfuRequestType::Vendor.into(),
        SET_INTERFACE,
        (setting >> 16) as u16,
        setting as u16,
    )?;
    // Test an invalid vendor request.
    expect_usb_bad_mode_write_control(
        &rescue,
        DfuRequestType::Vendor.into(),
        INVALID_INTERFACE,
        (setting >> 16) as u16,
        setting as u16,
    )?;
    // Test an invalid rescue mode with a standard SET_INTERFACE request.
    expect_usb_bad_mode_write_control(
        &rescue,
        DFU_REQUEST_TYPE_INTERFACE,
        USB_SETUP_REQ_SET_INTERFACE,
        (setting >> 16) as u16,
        setting as u16,
    )?;

    // Test an invalid interface request.
    expect_usb_bad_mode_write_control(
        &rescue,
        DFU_REQUEST_TYPE_INTERFACE,
        0_u8,
        (setting >> 16) as u16,
        setting as u16,
    )?;

    // Test a valid GET_INTERFACE request.
    rescue.write_control(
        DFU_REQUEST_TYPE_INTERFACE,
        USB_SETUP_REQ_GET_INTERFACE,
        (setting >> 16) as u16,
        setting as u16,
        &[],
    )?;

    // Test an unsupported setup request type.
    expect_usb_bad_mode_write_control(
        &rescue,
        0_u8,
        USB_SETUP_REQ_GET_INTERFACE,
        (setting >> 16) as u16,
        setting as u16,
    )?;

    rescue.reboot()?;

    let uart = transport.uart("console")?;
    UartConsole::wait_for(&*uart, r"Finished", Duration::from_secs(5))?;

    Ok(())
}

fn invalid_spi_flash_transaction(
    params: &RescueParams,
    transport: &TransportWrapper,
) -> Result<()> {
    let spi_params = SpiParams::default();
    let spi = spi_params.create(transport, "BOOTSTRAP")?;
    let rescue = SpiDfu::new(spi.clone(), params.clone());
    rescue.enter(transport, EntryMode::Reset)?;

    // Send an unsupported flash op code (CHIP_ERASE). The `rescue_protocol` on
    // the device will report `kErrorUsbBadSetup` in the mailbox.
    spi.run_eeprom_transactions(&mut [
        Transaction::Command(MODE_111.cmd(SpiFlash::RESET_ENABLE)),
        Transaction::Command(MODE_111.cmd(SpiFlash::CHIP_ERASE)),
    ])?;

    let sfdp = SpiFlash::read_sfdp(&*spi)?;
    let address_mode = AddressMode::from(sfdp.jedec.address_modes);

    // Send a packet where the offset (2040) + payload (256) exceeds the
    // device's 2KB buffer. The `rescue_protocol` should truncate the write.
    let payload = [0u8; 256];
    spi.run_eeprom_transactions(&mut [
        Transaction::Command(MODE_111.cmd(SpiFlash::WRITE_ENABLE)),
        Transaction::Write(
            MODE_111.cmd_addr(SpiFlash::PAGE_PROGRAM, 2040, address_mode),
            &payload,
        ),
        Transaction::WaitForBusyClear,
    ])?;

    // Send a payload of 300 bytes, which is larger than the SPI device's
    // maximum of 256 bytes.
    let payload_overflow = [0u8; 300];
    spi.run_eeprom_transactions(&mut [
        Transaction::Command(MODE_111.cmd(SpiFlash::WRITE_ENABLE)),
        Transaction::Write(
            MODE_111.cmd_addr(SpiFlash::PAGE_PROGRAM, 0, address_mode),
            &payload_overflow,
        ),
        Transaction::WaitForBusyClear,
    ])?;

    rescue.reboot()?;

    let uart = transport.uart("console")?;
    UartConsole::wait_for(&*uart, r"Finished", Duration::from_secs(5))?;

    Ok(())
}

fn usb_dfu_out_chunk_too_big(params: &RescueParams, transport: &TransportWrapper) -> Result<()> {
    let rescue = UsbDfu::new(params.clone());
    rescue.enter(transport, EntryMode::Reset)?;
    rescue.set_mode(RescueMode::RescueB)?;
    let chunk = vec![0u8; 2048];
    let chunk_too_big = vec![0u8; 4096];

    rescue.download(&chunk)?;
    let result = rescue.download(&chunk_too_big);

    if result.is_ok() {
        return Err(anyhow!("USB transaction should fail"));
    }

    rescue.reboot()?;

    let uart = transport.uart("console")?;
    UartConsole::wait_for(&*uart, r"Finished", Duration::from_secs(5))?;

    Ok(())
}

fn main() -> Result<()> {
    let opts = Opts::parse();
    opts.init.init_logging();
    let transport = opts.init.init_target()?;

    match opts.command {
        Commands::Rescue(rescue) => match rescue.action {
            DfuRescueTestActions::SpiDfuStateTransitions => {
                spi_dfu_state_transitions(&rescue.params, &transport)?
            }
            DfuRescueTestActions::InvalidSpiDfuRequests => {
                invalid_spi_dfu_requests(&rescue.params, &transport)?
            }
            DfuRescueTestActions::InvalidSpiFlashTransaction => {
                invalid_spi_flash_transaction(&rescue.params, &transport)?
            }
            DfuRescueTestActions::UsbDfuOutChunkTooBig => {
                usb_dfu_out_chunk_too_big(&rescue.params, &transport)?
            }
        },
    }

    Ok(())
}
