// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::{bail, Result};

use mio::{Registry, Token};
use std::borrow::Borrow;
use std::collections::HashMap;
use std::rc::Rc;
use std::time::Duration;

use super::errors::SerializedError;
use super::protocol::{
    EmuRequest, EmuResponse, GpioMonRequest, GpioMonResponse, GpioRequest, GpioResponse,
    I2cRequest, I2cResponse, I2cTransferRequest, I2cTransferResponse, Message, ProxyRequest,
    ProxyResponse, Request, Response, SpiRequest, SpiResponse, SpiTransferRequest,
    SpiTransferResponse, UartRequest, UartResponse,
};
use super::CommandHandler;
use crate::app::TransportWrapper;
use crate::bootstrap::Bootstrap;
use crate::io::gpio::GpioPin;
use crate::io::{i2c, nonblocking_help, spi};
use crate::proxy::nonblocking_uart::NonblockingUartRegistry;
use crate::transport::TransportError;

/// Implementation of the handling of each protocol request, by means of an underlying
/// `Transport` implementation.
pub struct TransportCommandHandler<'a> {
    transport: &'a TransportWrapper,
    nonblocking_help: Rc<dyn nonblocking_help::NonblockingHelp>,
    spi_chip_select: HashMap<String, Vec<spi::AssertChipSelect>>,
}

impl<'a> TransportCommandHandler<'a> {
    pub fn new(transport: &'a TransportWrapper) -> Result<Self> {
        let nonblocking_help = transport.nonblocking_help()?;
        Ok(Self {
            transport,
            nonblocking_help,
            spi_chip_select: HashMap::new(),
        })
    }

    fn optional_pin(&self, pin: &Option<String>) -> Result<Option<Rc<dyn GpioPin>>> {
        if let Some(pin) = pin {
            Ok(Some(self.transport.gpio_pin(pin)?))
        } else {
            Ok(None)
        }
    }

    /// This method will perform whatever action on the underlying `Transport` that is requested
    /// by the given `Request`, and return a response to be sent to the client.  Any `Err`
    /// return from this method will be propagated to the remote client, without any server-side
    /// logging.
    fn do_execute_cmd(
        &mut self,
        conn_token: Token,
        registry: &Registry,
        others: &mut NonblockingUartRegistry,
        req: &Request,
    ) -> Result<Response> {
        match req {
            Request::GetCapabilities => {
                Ok(Response::GetCapabilities(self.transport.capabilities()?))
            }
            Request::ApplyDefaultConfiguration => {
                self.transport.apply_default_configuration()?;
                Ok(Response::ApplyDefaultConfiguration)
            }
            Request::Gpio { id, command } => {
                let instance = self.transport.gpio_pin(id)?;
                match command {
                    GpioRequest::Read => {
                        let value = instance.read()?;
                        Ok(Response::Gpio(GpioResponse::Read { value }))
                    }
                    GpioRequest::Write { logic } => {
                        instance.write(*logic)?;
                        Ok(Response::Gpio(GpioResponse::Write))
                    }
                    GpioRequest::SetMode { mode } => {
                        instance.set_mode(*mode)?;
                        Ok(Response::Gpio(GpioResponse::SetMode))
                    }
                    GpioRequest::SetPullMode { pull } => {
                        instance.set_pull_mode(*pull)?;
                        Ok(Response::Gpio(GpioResponse::SetPullMode))
                    }
                }
            }
            Request::GpioMonitoring { command } => {
                let instance = self.transport.gpio_monitoring()?;
                match command {
                    GpioMonRequest::GetClockNature => {
                        let resp = instance.get_clock_nature()?;
                        Ok(Response::GpioMonitoring(GpioMonResponse::GetClockNature {
                            resp,
                        }))
                    }
                    GpioMonRequest::Start { pins } => {
                        let pins = self.transport.gpio_pins(pins)?;
                        let pins = pins.iter().map(Rc::borrow).collect::<Vec<&dyn GpioPin>>();
                        let resp = instance.monitoring_start(&pins)?;
                        Ok(Response::GpioMonitoring(GpioMonResponse::Start { resp }))
                    }
                    GpioMonRequest::Read {
                        pins,
                        continue_monitoring,
                    } => {
                        let pins = self.transport.gpio_pins(pins)?;
                        let pins = pins.iter().map(Rc::borrow).collect::<Vec<&dyn GpioPin>>();
                        let resp = instance.monitoring_read(&pins, *continue_monitoring)?;
                        Ok(Response::GpioMonitoring(GpioMonResponse::Read { resp }))
                    }
                }
            }
            Request::Uart { id, command } => {
                let instance = self.transport.uart(id)?;
                match command {
                    UartRequest::GetBaudrate => {
                        let rate = instance.get_baudrate()?;
                        Ok(Response::Uart(UartResponse::GetBaudrate { rate }))
                    }
                    UartRequest::SetBaudrate { rate } => {
                        instance.set_baudrate(*rate)?;
                        Ok(Response::Uart(UartResponse::SetBaudrate))
                    }
                    UartRequest::Read {
                        timeout_millis,
                        len,
                    } => {
                        let mut data = vec![0u8; *len as usize];
                        let count = match timeout_millis {
                            None => instance.read(&mut data)?,
                            Some(ms) => instance
                                .read_timeout(&mut data, Duration::from_millis(*ms as u64))?,
                        };
                        data.resize(count, 0);
                        Ok(Response::Uart(UartResponse::Read { data }))
                    }
                    UartRequest::Write { data } => {
                        instance.write(data)?;
                        Ok(Response::Uart(UartResponse::Write))
                    }
                    UartRequest::SupportsNonblockingRead => {
                        let has_support = instance.supports_nonblocking_read()?;
                        Ok(Response::Uart(UartResponse::SupportsNonblockingRead {
                            has_support,
                        }))
                    }
                    UartRequest::RegisterNonblockingRead => {
                        let channel =
                            others.nonblocking_uart_init(&instance, conn_token, registry)?;
                        Ok(Response::Uart(UartResponse::RegisterNonblockingRead {
                            channel,
                        }))
                    }
                }
            }
            Request::Spi { id, command } => {
                let instance = self.transport.spi(id)?;
                match command {
                    SpiRequest::GetTransferMode => {
                        let mode = instance.get_transfer_mode()?;
                        Ok(Response::Spi(SpiResponse::GetTransferMode { mode }))
                    }
                    SpiRequest::SetTransferMode { mode } => {
                        instance.set_transfer_mode(*mode)?;
                        Ok(Response::Spi(SpiResponse::SetTransferMode))
                    }
                    SpiRequest::GetBitsPerWord => {
                        let bits_per_word = instance.get_bits_per_word()?;
                        Ok(Response::Spi(SpiResponse::GetBitsPerWord { bits_per_word }))
                    }
                    SpiRequest::SetBitsPerWord { bits_per_word } => {
                        instance.set_bits_per_word(*bits_per_word)?;
                        Ok(Response::Spi(SpiResponse::SetBitsPerWord))
                    }
                    SpiRequest::GetMaxSpeed => {
                        let speed = instance.get_max_speed()?;
                        Ok(Response::Spi(SpiResponse::GetMaxSpeed { speed }))
                    }
                    SpiRequest::SetMaxSpeed { value } => {
                        instance.set_max_speed(*value)?;
                        Ok(Response::Spi(SpiResponse::SetMaxSpeed))
                    }
                    SpiRequest::SupportsBidirectionalTransfer => {
                        let has_support = instance.supports_bidirectional_transfer()?;
                        Ok(Response::Spi(SpiResponse::SupportsBidirectionalTransfer {
                            has_support,
                        }))
                    }
                    SpiRequest::SetPins {
                        serial_clock,
                        host_out_device_in,
                        host_in_device_out,
                        chip_select,
                    } => {
                        instance.set_pins(
                            self.optional_pin(serial_clock)?.as_ref(),
                            self.optional_pin(host_out_device_in)?.as_ref(),
                            self.optional_pin(host_in_device_out)?.as_ref(),
                            self.optional_pin(chip_select)?.as_ref(),
                        )?;
                        Ok(Response::Spi(SpiResponse::SetPins))
                    }
                    SpiRequest::GetMaxTransferCount => {
                        let number = instance.get_max_transfer_count()?;
                        Ok(Response::Spi(SpiResponse::GetMaxTransferCount { number }))
                    }
                    SpiRequest::GetMaxTransferSizes => {
                        let sizes = instance.get_max_transfer_sizes()?;
                        Ok(Response::Spi(SpiResponse::GetMaxTransferSizes { sizes }))
                    }
                    SpiRequest::GetEepromMaxTransferSizes => {
                        let sizes = instance.get_eeprom_max_transfer_sizes()?;
                        Ok(Response::Spi(SpiResponse::GetEepromMaxTransferSizes {
                            sizes,
                        }))
                    }
                    SpiRequest::SetVoltage { voltage } => {
                        instance.set_voltage(*voltage)?;
                        Ok(Response::Spi(SpiResponse::SetVoltage))
                    }
                    SpiRequest::RunTransaction { transaction: reqs } => {
                        // Construct proper response to each transfer in request.
                        let mut resps: Vec<SpiTransferResponse> = reqs
                            .iter()
                            .map(|transfer| match transfer {
                                SpiTransferRequest::Read { len } => SpiTransferResponse::Read {
                                    data: vec![0; *len as usize],
                                },
                                SpiTransferRequest::Write { .. } => SpiTransferResponse::Write,
                                SpiTransferRequest::Both { data } => SpiTransferResponse::Both {
                                    data: vec![0; data.len()],
                                },
                            })
                            .collect();
                        // Now carefully craft a proper parameter to the
                        // `spi::Target::run_transactions()` method.  It will have reference
                        // into elements of both the request vector and mutable reference into
                        // the response vector.
                        let mut transaction: Vec<spi::Transfer> = reqs
                            .iter()
                            .zip(resps.iter_mut())
                            .map(|pair| match pair {
                                (
                                    SpiTransferRequest::Read { .. },
                                    SpiTransferResponse::Read { data },
                                ) => spi::Transfer::Read(data),
                                (
                                    SpiTransferRequest::Write { data },
                                    SpiTransferResponse::Write,
                                ) => spi::Transfer::Write(data),
                                (
                                    SpiTransferRequest::Both { data: wdata },
                                    SpiTransferResponse::Both { data },
                                ) => spi::Transfer::Both(wdata, data),
                                _ => {
                                    // This can only happen if the logic in this method is
                                    // flawed.  (Never due to network input.)
                                    panic!("Mismatch");
                                }
                            })
                            .collect();
                        instance.run_transaction(&mut transaction)?;
                        Ok(Response::Spi(SpiResponse::RunTransaction {
                            transaction: resps,
                        }))
                    }
                    SpiRequest::AssertChipSelect => {
                        // Add a `spi::AssertChipSelect` object to the stack for this particular
                        // SPI instance.
                        self.spi_chip_select
                            .entry(id.to_string())
                            .or_default()
                            .push(instance.assert_cs()?);
                        Ok(Response::Spi(SpiResponse::AssertChipSelect))
                    }
                    SpiRequest::DeassertChipSelect => {
                        // Remove a `spi::AssertChipSelect` object from the stack for this
                        // particular SPI instance.
                        self.spi_chip_select
                            .get_mut(id)
                            .ok_or(TransportError::InvalidOperation)?
                            .pop()
                            .ok_or(TransportError::InvalidOperation)?;
                        Ok(Response::Spi(SpiResponse::DeassertChipSelect))
                    }
                }
            }
            Request::I2c { id, command } => {
                let instance = self.transport.i2c(id)?;
                match command {
                    I2cRequest::GetMaxSpeed => {
                        let speed = instance.get_max_speed()?;
                        Ok(Response::I2c(I2cResponse::GetMaxSpeed { speed }))
                    }
                    I2cRequest::SetMaxSpeed { value } => {
                        instance.set_max_speed(*value)?;
                        Ok(Response::I2c(I2cResponse::SetMaxSpeed))
                    }
                    I2cRequest::RunTransaction {
                        address,
                        transaction: reqs,
                    } => {
                        // Construct proper response to each transfer in request.
                        let mut resps: Vec<I2cTransferResponse> = reqs
                            .iter()
                            .map(|transfer| match transfer {
                                I2cTransferRequest::Read { len } => I2cTransferResponse::Read {
                                    data: vec![0; *len as usize],
                                },
                                I2cTransferRequest::Write { .. } => I2cTransferResponse::Write,
                            })
                            .collect();
                        // Now carefully craft a proper parameter to the
                        // `i2c::Bus::run_transactions()` method.  It will have reference
                        // into elements of both the request vector and mutable reference into
                        // the response vector.
                        let mut transaction: Vec<i2c::Transfer> = reqs
                            .iter()
                            .zip(resps.iter_mut())
                            .map(|pair| match pair {
                                (
                                    I2cTransferRequest::Read { .. },
                                    I2cTransferResponse::Read { data },
                                ) => i2c::Transfer::Read(data),
                                (
                                    I2cTransferRequest::Write { data },
                                    I2cTransferResponse::Write,
                                ) => i2c::Transfer::Write(data),
                                _ => {
                                    // This can only happen if the logic in this method is
                                    // flawed.  (Never due to network input.)
                                    panic!("Mismatch");
                                }
                            })
                            .collect();
                        instance.run_transaction(*address, &mut transaction)?;
                        Ok(Response::I2c(I2cResponse::RunTransaction {
                            transaction: resps,
                        }))
                    }
                }
            }
            Request::Emu { command } => {
                let instance = self.transport.emulator()?;
                match command {
                    EmuRequest::GetState => Ok(Response::Emu(EmuResponse::GetState {
                        state: instance.get_state()?,
                    })),
                    EmuRequest::Start {
                        factory_reset,
                        args,
                    } => {
                        instance.start(*factory_reset, args)?;
                        Ok(Response::Emu(EmuResponse::Start))
                    }
                    EmuRequest::Stop => {
                        instance.stop()?;
                        Ok(Response::Emu(EmuResponse::Stop))
                    }
                }
            }
            Request::Proxy(command) => match command {
                ProxyRequest::Provides {} => {
                    let provides_map = self.transport.provides_map()?.clone();
                    Ok(Response::Proxy(ProxyResponse::Provides { provides_map }))
                }
                ProxyRequest::Bootstrap { options, payload } => {
                    Bootstrap::update(self.transport, options, payload)?;
                    Ok(Response::Proxy(ProxyResponse::Bootstrap))
                }
                ProxyRequest::ApplyPinStrapping { strapping_name } => {
                    self.transport.pin_strapping(strapping_name)?.apply()?;
                    Ok(Response::Proxy(ProxyResponse::ApplyPinStrapping))
                }
                ProxyRequest::RemovePinStrapping { strapping_name } => {
                    self.transport.pin_strapping(strapping_name)?.remove()?;
                    Ok(Response::Proxy(ProxyResponse::RemovePinStrapping))
                }
            },
        }
    }
}

impl<'a> CommandHandler<Message, NonblockingUartRegistry> for TransportCommandHandler<'a> {
    /// This method will perform whatever action on the underlying `Transport` that is requested
    /// by the given `Message`, and return a response to be sent to the client.  Any `Err`
    /// return from this method will be treated as an irrecoverable protocol error, causing an
    /// error message in the server log, and the connection to be terminated.
    fn execute_cmd(
        &mut self,
        conn_token: Token,
        registry: &Registry,
        others: &mut NonblockingUartRegistry,
        msg: &Message,
    ) -> Result<Message> {
        if let Message::Req(req) = msg {
            // Package either `Ok()` or `Err()` into a `Message`, to be sent via network.
            return Ok(Message::Res(
                self.do_execute_cmd(conn_token, registry, others, req)
                    .map_err(SerializedError::from),
            ));
        }
        bail!("Client sent non-Request to server!!!");
    }

    fn register_nonblocking_help(&self, registry: &mio::Registry, token: mio::Token) -> Result<()> {
        self.nonblocking_help
            .register_nonblocking_help(registry, token)
    }

    fn nonblocking_help(&self) -> Result<()> {
        self.nonblocking_help.nonblocking_help()
    }
}
