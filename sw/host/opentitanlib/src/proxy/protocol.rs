// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use serde::{Deserialize, Serialize};

use crate::io::gpio::{PinMode, PullMode};
use crate::io::spi::TransferMode;
use crate::transport::TransportError;
use crate::util::voltage::Voltage;

#[derive(Serialize, Deserialize)]
pub enum Message {
    Req(Request),
    Res(Result<Response, TransportError>),
}

#[derive(Serialize, Deserialize)]
pub enum Request {
    Gpio { id: String, command: GpioRequest },
    Uart { id: String, command: UartRequest },
    Spi { id: String, command: SpiRequest },
    I2c { id: String, command: I2cRequest },
}

#[derive(Serialize, Deserialize)]
pub enum Response {
    Gpio(GpioResponse),
    Uart(UartResponse),
    Spi(SpiResponse),
    I2c(I2cResponse),
}

#[derive(Serialize, Deserialize)]
pub enum GpioRequest {
    Write { logic: bool },
    Read,
    SetMode { mode: PinMode },
    SetPullMode { pull: PullMode },
}

#[derive(Serialize, Deserialize)]
pub enum GpioResponse {
    Write,
    Read { value: bool },
    SetMode,
    SetPullMode,
}

#[derive(Serialize, Deserialize)]
pub enum UartRequest {
    GetBaudrate,
    SetBaudrate {
        rate: u32,
    },
    Read {
        timeout_millis: Option<u32>,
        len: u32,
    },
    Write {
        data: Vec<u8>,
    },
}

#[derive(Serialize, Deserialize)]
pub enum UartResponse {
    GetBaudrate { rate: u32 },
    SetBaudrate,
    Read { data: Vec<u8> },
    Write,
}

#[derive(Serialize, Deserialize)]
pub enum SpiTransferRequest {
    Read { len: u32 },
    Write { data: Vec<u8> },
    Both { data: Vec<u8> },
}

#[derive(Serialize, Deserialize)]
pub enum SpiTransferResponse {
    Read { data: Vec<u8> },
    Write,
    Both { data: Vec<u8> },
}

#[derive(Serialize, Deserialize)]
pub enum SpiRequest {
    GetTransferMode,
    SetTransferMode {
        mode: TransferMode,
    },
    GetBitsPerWord,
    SetBitsPerWord {
        bits_per_word: u32,
    },
    GetMaxSpeed,
    SetMaxSpeed {
        value: u32,
    },
    GetMaxTransferCount,
    GetMaxChunkSize,
    SetVoltage {
        voltage: Voltage,
    },
    RunTransaction {
        transaction: Vec<SpiTransferRequest>,
    },
}

#[derive(Serialize, Deserialize)]
pub enum SpiResponse {
    GetTransferMode {
        mode: TransferMode,
    },
    SetTransferMode,
    GetBitsPerWord {
        bits_per_word: u32,
    },
    SetBitsPerWord,
    GetMaxSpeed {
        speed: u32,
    },
    SetMaxSpeed,
    GetMaxTransferCount {
        number: usize,
    },
    GetMaxChunkSize {
        size: usize,
    },
    SetVoltage,
    RunTransaction {
        transaction: Vec<SpiTransferResponse>,
    },
}

#[derive(Serialize, Deserialize)]
pub enum I2cTransferRequest {
    Read { len: u32 },
    Write { data: Vec<u8> },
}

#[derive(Serialize, Deserialize)]
pub enum I2cTransferResponse {
    Read { data: Vec<u8> },
    Write,
}

#[derive(Serialize, Deserialize)]
pub enum I2cRequest {
    RunTransaction {
        address: u8,
        transaction: Vec<I2cTransferRequest>,
    },
}

#[derive(Serialize, Deserialize)]
pub enum I2cResponse {
    RunTransaction {
        transaction: Vec<I2cTransferResponse>,
    },
}
