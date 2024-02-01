// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::{anyhow, Result};
use mio::net::TcpStream;
use num_enum::TryFromPrimitive;
use opentitanlib::tpm::Driver;
use std::io::{Read, Write};
use std::net::Shutdown;

pub(crate) const CMD_SIZE: usize = std::mem::size_of::<TcpTpmCommands>();
const SERVER_VERSION: u32 = 1;

#[derive(TryFromPrimitive, Debug)]
#[repr(u32)]
pub(crate) enum TcpTpmCommands {
    SignalPowerOn = 1,
    SignalPowerOff = 2,
    SignalPPOn = 3,
    SignalPPOff = 4,
    SignalHashStart = 5,
    SignalHashData = 6,
    SignalHashEnd = 7,
    SendCommand = 8,
    SignalCancelOn = 9,
    SignalCancelOff = 10,
    SignalNvOn = 11,
    SignalNvOff = 12,
    SignalKeyCacheOn = 13,
    SignalKeyCacheOff = 14,
    RemoteHandshake = 15,
    //SetAlternativeResult = 16,    // Not used since 1.38h
    SessionEnd = 20,
    Stop = 21,
    ActGetSignaled = 26,
    TestFailureMode = 30,
}

/// Platform hierarchy is enabled, and hardware platform functionality (such
/// as SignalHashStart/Data/End) is available.
const PLATFORM_AVAILABLE: u32 = 0x01;

/// The device is TPM Resource Manager (TRM), rather than a raw TPM.
/// This means context management commands are unavailable, and the handle values
/// returned to the client are virtualized.
const _USES_TBS: u32 = 0x02;

/// The TRM is in raw mode (i.e. no actual resourse virtualization is performed).
const _IN_RAW_MODE: u32 = 0x04;

/// Physical presence signals (SignalPPOn/Off) are supported.
const _SUPPORTS_PP: u32 = 0x08;

/// Valid only with PlatformAvailable set.
/// System and TPM power control signals (SignalPowerOn/Off) are not supported.
const NO_POWER_CTL: u32 = 0x10;

/// Valid only with tpmPlatformAvailable set.
/// TPM locality cannot be changed.
const NO_LOCALITY_CTL: u32 = 0x20;

/// Valid only with tpmPlatformAvailable set.
/// NV control signals (SignalNvOn/Off) are not supported.
const NO_NV_CTL: u32 = 0x40;

/// Serve the command port for the TPM, forwarding commands to the bus specified in `opts`.
pub(crate) fn serve_command(stream: &mut TcpStream, tpm: &dyn Driver) -> Result<bool> {
    let mut data = [0u8; CMD_SIZE];
    let len = stream.read(&mut data)?;
    if len == 0 {
        stream.shutdown(Shutdown::Both)?;
        return Ok(true);
    }
    let cmd_u32 = u32::from_be_bytes(data);
    let cmd = TcpTpmCommands::try_from_primitive(cmd_u32)?;
    if matches!(cmd, TcpTpmCommands::SessionEnd) {
        stream.shutdown(Shutdown::Both)?;
        Ok(true)
    } else {
        handle_cmd(cmd, stream, tpm).map(|_| false)
    }
}

/// Handle the requested command and send the reply on `stream`. If this it a TPM command, send it
/// to `tpm`.
fn handle_cmd(cmd: TcpTpmCommands, stream: &mut TcpStream, tpm: &dyn Driver) -> Result<()> {
    const CFG: u32 = PLATFORM_AVAILABLE | NO_POWER_CTL | NO_LOCALITY_CTL | NO_NV_CTL;
    log::info!("CMD {:?}", cmd);
    match cmd {
        TcpTpmCommands::RemoteHandshake => {
            let mut ver = [0u8; 4];
            stream.read_exact(&mut ver)?;
            log::debug!("Client ver {}.", u32::from_be_bytes(ver));
            stream.write_all(&SERVER_VERSION.to_be_bytes())?;
            // TODO Make TpmEndpointInfo a bitfield and send
            stream.write_all(&CFG.to_be_bytes())?;
            stream.write_all(&[0u8; 4])?;
            Ok(())
        }
        TcpTpmCommands::SendCommand => handle_send(stream, tpm),
        _ => {
            let _ = stream.write(&[0u8; 4])?;
            Ok(())
        }
    }
}

/// Forward a TPM command to the device and send the reponse back to `stream`.
fn handle_send(stream: &mut TcpStream, tpm: &dyn Driver) -> Result<()> {
    let mut locality = [0u8; 1];
    let mut sz = [0u8; 4];
    stream.read_exact(&mut locality)?;
    stream.read_exact(&mut sz)?;
    let sz = u32::from_be_bytes(sz) as usize;

    let mut cmd: Vec<u8> = vec![0; sz];
    let cmd_sz = stream.read(&mut cmd)?;

    if cmd_sz != sz {
        return Err(anyhow!("Bad command size."));
    }

    log::debug!("TPM cmd {:02x?}", cmd);
    match tpm.execute_command(&cmd) {
        Ok(res) => {
            stream.write_all(&(res.len() as u32).to_be_bytes())?;
            stream.write_all(&res)?;
            stream.write_all(&[0u8; 4])?;
        }
        Err(e) => {
            log::error!("Command fail: {}", e);
            stream.write_all(&[0u8; 4])?;
            stream.write_all(&[0u8; 4])?;
        }
    }

    Ok(())
}
