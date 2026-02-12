// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use std::io::ErrorKind;

use anyhow::{Context, Result};
use opentitanlib::tpm::Driver;
use tokio::io::{AsyncReadExt, AsyncWriteExt};
use tokio::net::TcpStream;

const SERVER_VERSION: u32 = 1;

#[derive(strum::FromRepr, Debug)]
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
pub(crate) async fn serve_command(stream: &mut TcpStream, tpm: &dyn Driver) -> Result<()> {
    loop {
        let cmd_u32 = match stream.read_u32().await {
            Err(err) if err.kind() == ErrorKind::UnexpectedEof => break,
            v => v?,
        };

        let cmd = TcpTpmCommands::from_repr(cmd_u32)
            .with_context(|| format!("invalid TCP TMP command value {cmd_u32:#010x}"))?;
        if matches!(cmd, TcpTpmCommands::SessionEnd) {
            break;
        }

        handle_cmd(cmd, stream, tpm).await?;
    }

    stream.shutdown().await?;
    Ok(())
}

/// Handle the requested command and send the reply on `stream`. If this it a TPM command, send it
/// to `tpm`.
async fn handle_cmd(cmd: TcpTpmCommands, stream: &mut TcpStream, tpm: &dyn Driver) -> Result<()> {
    const CFG: u32 = PLATFORM_AVAILABLE | NO_POWER_CTL | NO_LOCALITY_CTL | NO_NV_CTL;
    log::info!("CMD {:?}", cmd);
    match cmd {
        TcpTpmCommands::RemoteHandshake => {
            let ver = stream.read_u32().await?;
            log::debug!("Client ver {}.", ver);
            stream.write_u32(SERVER_VERSION).await?;
            // TODO Make TpmEndpointInfo a bitfield and send
            stream.write_u32(CFG).await?;
            stream.write_u32(0).await?;
            Ok(())
        }
        TcpTpmCommands::SendCommand => handle_send(stream, tpm).await,
        _ => {
            stream.write_u32(0).await?;
            Ok(())
        }
    }
}

/// Forward a TPM command to the device and send the reponse back to `stream`.
async fn handle_send(stream: &mut TcpStream, tpm: &dyn Driver) -> Result<()> {
    let _locality = stream.read_u8().await?;
    let sz = stream.read_u32().await? as usize;

    let mut cmd: Vec<u8> = vec![0; sz];
    stream.read_exact(&mut cmd).await?;

    log::debug!("TPM cmd {:02x?}", cmd);
    match tpm.execute_command(&cmd) {
        Ok(res) => {
            stream.write_u32(res.len() as u32).await?;
            stream.write_all(&res).await?;
            stream.write_u32(0).await?;
        }
        Err(e) => {
            log::error!("Command fail: {}", e);
            stream.write_u32(0).await?;
            stream.write_u32(0).await?;
        }
    }

    Ok(())
}
