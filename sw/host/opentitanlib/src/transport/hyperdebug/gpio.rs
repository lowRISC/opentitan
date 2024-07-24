// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::{bail, ensure, Result};
use byteorder::{LittleEndian, ReadBytesExt, WriteBytesExt};
use once_cell::sync::Lazy;
use regex::Regex;
use std::io::Cursor;
use std::mem::size_of;
use std::rc::Rc;
use std::time::Duration;
use zerocopy::{FromBytes, FromZeroes};

use crate::io::gpio::{
    BitbangEntry, ClockNature, Edge, GpioBitbanging, GpioError, GpioMonitoring, GpioPin,
    MonitoringEvent, MonitoringReadResponse, MonitoringStartResponse, PinMode, PullMode,
};
use crate::transport::hyperdebug::{BulkInterface, CommandHandler, Inner};
use crate::transport::TransportError;

pub struct HyperdebugGpioPin {
    console: CommandHandler,
    pinname: String,
}

impl HyperdebugGpioPin {
    pub fn open(console: &CommandHandler, pinname: &str) -> Result<Self> {
        let result = Self {
            console: console.clone(),
            pinname: pinname.to_string(),
        };
        Ok(result)
    }
}

impl GpioPin for HyperdebugGpioPin {
    /// Reads the value of the GPIO pin `id`.
    fn read(&self) -> Result<bool> {
        let line = self
            .console
            .cmd_one_line_output(&format!("gpioget {}", &self.pinname))?;
        Ok(line.trim_start().starts_with('1'))
    }

    /// Sets the value of the GPIO pin `id` to `value`.
    fn write(&self, value: bool) -> Result<()> {
        self.console
            .cmd_no_output(&format!("gpioset {} {}", &self.pinname, u32::from(value)))
    }

    fn set_mode(&self, mode: PinMode) -> Result<()> {
        self.console.cmd_no_output(&format!(
            "gpiomode {} {}",
            &self.pinname,
            match mode {
                PinMode::Input => "input",
                PinMode::OpenDrain => "opendrain",
                PinMode::PushPull => "pushpull",
                PinMode::AnalogInput => "adc",
                PinMode::AnalogOutput => "dac",
                PinMode::Alternate => "alternate",
            }
        ))
    }

    fn set_pull_mode(&self, mode: PullMode) -> Result<()> {
        self.console.cmd_no_output(&format!(
            "gpiopullmode {} {}",
            &self.pinname,
            match mode {
                PullMode::None => "none",
                PullMode::PullUp => "up",
                PullMode::PullDown => "down",
            }
        ))
    }

    fn analog_read(&self) -> Result<f32> {
        let line = self
            .console
            .cmd_one_line_output(&format!("adc {}", &self.pinname))
            .map_err(|_| TransportError::CommunicationError("No output from adc".to_string()))?;
        static ADC_REGEX: Lazy<Regex> =
            Lazy::new(|| Regex::new("^ +([^ ])+ = ([0-9]+) mV").unwrap());
        if let Some(captures) = ADC_REGEX.captures(&line) {
            let milli_volts: u32 = captures.get(2).unwrap().as_str().parse()?;
            Ok(milli_volts as f32 / 1000.0)
        } else {
            Err(TransportError::CommunicationError("Unrecognized adc output".to_string()).into())
        }
    }

    fn analog_write(&self, volts: f32) -> Result<()> {
        if !(0.0..=3.3).contains(&volts) {
            return Err(GpioError::UnsupportedPinVoltage(volts).into());
        }
        let milli_volts = (volts * 1000.0) as u32;
        self.console.cmd_no_output(&format!(
            "gpio analog-set {} {}",
            &self.pinname, milli_volts,
        ))
    }

    fn set(
        &self,
        mode: Option<PinMode>,
        value: Option<bool>,
        pull: Option<PullMode>,
        volts: Option<f32>,
    ) -> Result<()> {
        if let Some(v) = volts {
            if !(0.0..=3.3).contains(&v) {
                return Err(GpioError::UnsupportedPinVoltage(v).into());
            }
        }
        self.console.cmd_no_output(&format!(
            "gpio multiset {} {} {} {} {}",
            &self.pinname,
            match value {
                Some(false) => "0",
                Some(true) => "1",
                None => "-",
            },
            match mode {
                Some(PinMode::Input) => "input",
                Some(PinMode::OpenDrain) => "opendrain",
                Some(PinMode::PushPull) => "pushpull",
                Some(PinMode::AnalogInput) => "adc",
                Some(PinMode::AnalogOutput) => "dac",
                Some(PinMode::Alternate) => "alternate",
                None => "-",
            },
            match pull {
                Some(PullMode::None) => "none",
                Some(PullMode::PullUp) => "up",
                Some(PullMode::PullDown) => "down",
                None => "-",
            },
            if let Some(v) = volts {
                format!("{}", (v * 1000.0) as u32)
            } else {
                "-".to_string()
            },
        ))
    }

    fn get_internal_pin_name(&self) -> Option<&str> {
        Some(&self.pinname)
    }
}

const USB_MAX_SIZE: usize = 64;

/// HyperDebug supports retreiving a transcript of events on a set of monitored GPIO pins either
/// through its textual console, or for improved performance, through a vendor extension to the
/// binary CMSIS-DAP endpoint.
///
/// This struct describes the binary header of the response (following the one-byte CMSIS-DAP
/// response header), after which the transcript data will follow.  The protocol is designed to
/// allow HyperDebug to pretty much dump the contents of its internal buffer to the USB interface.
///
/// The data part consists of a sequence of integers in leb128 encoding.  Each integer contains
/// the index of the signal that changed in the low bits, and the number of microseconds since
/// last event in the high bits.  The number of bits used for encoding the signal depends on how
/// many signals are monitored.
///
/// The source for the HyperDebug firmware generating these responses is here:
/// https://chromium.googlesource.com/chromiumos/platform/ec/+/refs/heads/main/board/hyperdebug/gpio.c
#[derive(FromBytes, FromZeroes, Debug)]
#[repr(C)]
struct RspGpioMonitoringHeader {
    /// Size of the header as sent by HyperDebug (excluding one byte CMSIS-DAP header), will be at
    /// least `size_of::<RspGpioMonitoringHeader>`, but future versions could add more header
    /// fields.
    struct_size: u16,
    /// Status/error code, zero means success.
    status: u16,
    /// Bitfield containing the levels of the monitored signals as of the begining of the
    /// transcript about to be sent, starting from the lest significant bit.
    start_levels: u16,
    /// Number of data bytes following this header.
    transcript_size: u16,
    /// Timestamp when the monitoring was originally started (will be the same in subsequent
    /// responses).
    start_timestamp: u64,
    /// Timestamp when the current transcript ends (will be different in subsequenct responses).
    end_timestamp: u64,
}

pub struct HyperdebugGpioMonitoring {
    console: CommandHandler,
    inner: Rc<Inner>,
    cmsis_interface: Option<BulkInterface>,
}

impl HyperdebugGpioMonitoring {
    /// CMSIS extension for HyperDebug GPIO.
    const CMSIS_DAP_CUSTOM_COMMAND_GPIO: u8 = 0x83;

    /// Sub-command for reading list of GPIO edge events
    const GPIO_MONITORING_READ: u8 = 0x00;

    // Some of the possible values for RspGpioMonitoringHeader.status
    const MON_SUCCESS: u16 = 0;
    const MON_BUFFER_OVERRUN: u16 = 5;

    pub fn open(
        console: &CommandHandler,
        inner: &Rc<Inner>,
        cmsis_interface: Option<BulkInterface>,
    ) -> Result<Self> {
        Ok(Self {
            console: console.clone(),
            inner: Rc::clone(inner),
            cmsis_interface,
        })
    }
}

impl GpioMonitoring for HyperdebugGpioMonitoring {
    fn get_clock_nature(&self) -> Result<ClockNature> {
        Ok(ClockNature::Wallclock {
            resolution: 1_000_000,
            offset: None,
        })
    }

    /// Set up edge trigger detection on the given set of pins, transport will buffer the list
    /// internally.
    fn monitoring_start(&self, pins: &[&dyn GpioPin]) -> Result<MonitoringStartResponse> {
        let mut pin_names = Vec::new();
        for pin in pins {
            pin_names.push(
                pin.get_internal_pin_name()
                    .ok_or(TransportError::InvalidOperation)?,
            );
        }
        static START_TIME_REGEX: Lazy<Regex> = Lazy::new(|| Regex::new("^ +@([0-9]+)").unwrap());
        static SIGNAL_REGEX: Lazy<Regex> =
            Lazy::new(|| Regex::new("^ +([0-9]+) ([^ ])+ ([01])").unwrap());
        let mut start_time: u64 = 0;
        let mut signals = Vec::new();
        let mut unexpected_output = false;
        self.console.execute_command(
            &format!("gpio monitoring start {}", pin_names.join(" ")),
            |line| {
                if let Some(captures) = START_TIME_REGEX.captures(line) {
                    start_time = captures.get(1).unwrap().as_str().parse().unwrap();
                } else if let Some(captures) = SIGNAL_REGEX.captures(line) {
                    signals.push(captures.get(3).unwrap().as_str() != "0");
                } else {
                    unexpected_output = true;
                    log::error!("Unexpected HyperDebug output: {}\n", line);
                };
            },
        )?;
        if unexpected_output {
            bail!(TransportError::CommunicationError(
                "Unrecognized response".to_string()
            ))
        }
        Ok(MonitoringStartResponse {
            timestamp: start_time,
            initial_levels: signals,
        })
    }

    /// Retrieve list of events detected thus far, optionally stopping the possibly expensive edge
    /// detection.  Buffer overrun will be reported as an `Err`, and result in the stopping of the
    /// edge detection irrespective of the parameter value.
    fn monitoring_read(
        &self,
        pins: &[&dyn GpioPin],
        continue_monitoring: bool,
    ) -> Result<MonitoringReadResponse> {
        let mut pin_names = Vec::new();
        for pin in pins {
            pin_names.push(
                pin.get_internal_pin_name()
                    .ok_or(TransportError::InvalidOperation)?,
            );
        }

        if let Some(cmsis_interface) = self.cmsis_interface {
            // HyperDebug firmware supports binary protocol for retrieving list of events, use
            // that for greatly improved performance.

            let mut pkt = Vec::<u8>::new();
            pkt.write_u8(Self::CMSIS_DAP_CUSTOM_COMMAND_GPIO)?;
            pkt.write_u8(Self::GPIO_MONITORING_READ)?;
            pkt.write_u8(pin_names.len().try_into()?)?;
            for pin_name in &pin_names {
                pkt.write_u8(pin_name.len().try_into()?)?;
                pkt.extend_from_slice(pin_name.as_bytes());
            }
            self.inner
                .usb_device
                .borrow()
                .write_bulk(cmsis_interface.out_endpoint, &pkt)?;

            let mut databytes: Vec<u8> =
                vec![0u8; 1 + size_of::<RspGpioMonitoringHeader>() + USB_MAX_SIZE];
            let mut bytecount = 0;

            while bytecount < 1 + size_of::<RspGpioMonitoringHeader>() {
                let read_count = self.inner.usb_device.borrow().read_bulk(
                    cmsis_interface.in_endpoint,
                    &mut databytes[bytecount..][..USB_MAX_SIZE],
                )?;
                ensure!(
                    read_count > 0,
                    TransportError::CommunicationError("Truncated GPIO response".to_string())
                );
                bytecount += read_count;
            }
            ensure!(
                databytes[0] == Self::CMSIS_DAP_CUSTOM_COMMAND_GPIO,
                TransportError::CommunicationError(
                    "Unrecognized CMSIS-DAP response to GPIO request".to_string()
                )
            );
            let resp: RspGpioMonitoringHeader =
                FromBytes::read_from_prefix(&databytes[1..]).unwrap();
            ensure!(
                resp.struct_size as usize >= size_of::<RspGpioMonitoringHeader>(),
                TransportError::CommunicationError(
                    "Short CMSIS-DAP response to GPIO request".to_string()
                )
            );
            let header_bytes = resp.struct_size as usize + 1;
            databytes.resize(header_bytes + resp.transcript_size as usize, 0u8);

            while bytecount < databytes.len() {
                let c = self
                    .inner
                    .usb_device
                    .borrow()
                    .read_bulk(cmsis_interface.in_endpoint, &mut databytes[bytecount..])?;
                bytecount += c;
            }

            match resp.status {
                Self::MON_SUCCESS => (),
                Self::MON_BUFFER_OVERRUN => bail!(TransportError::CommunicationError(
                    "HyperDebug GPIO monitoring buffer overrun".to_string()
                )),
                n => bail!(TransportError::CommunicationError(format!(
                    "Unexpected HyperDebug GPIO error: {}",
                    n
                ))),
            }

            // Figure out how many of the low bits are used for storing the index of the signal
            // hanving changed. (If only one signal, no bits are used, if two signals, then one
            // bit is used, if three or four, then two bits are used, etc.)
            let signal_bits = 32 - (pin_names.len() as u32 - 1).leading_zeros();
            let signal_mask = (1u64 << signal_bits) - 1;

            let mut cur_time: u64 = resp.start_timestamp;
            let mut cur_levels = resp.start_levels;
            let mut events = Vec::new();
            let mut idx = header_bytes;

            // Now decode the list of events, each consisting of a variable legnth encoded 64-bit
            // integer.
            while idx < databytes.len() {
                let value = decode_leb128(&mut idx, &databytes)?;

                // The 64-bit value consists of two parts, the lower `signal_bits` bits indicate
                // which signal had an edge, the upper bits indicate the number of microseconds
                // since the previous event (on any signal, not necessarily on that same one).
                cur_time += value >> signal_bits;
                let signal_index = (value & signal_mask) as u8;
                cur_levels ^= 1 << signal_index;
                events.push(MonitoringEvent {
                    signal_index,
                    edge: if cur_levels & (1 << signal_index) == 0 {
                        Edge::Falling
                    } else {
                        Edge::Rising
                    },
                    timestamp: cur_time,
                });
            }

            if !continue_monitoring {
                self.console
                    .cmd_no_output(&format!("gpio monitoring stop {}", pin_names.join(" ")))?;
            }
            return Ok(MonitoringReadResponse {
                events,
                timestamp: resp.end_timestamp,
            });
        }

        static START_TIME_REGEX: Lazy<Regex> = Lazy::new(|| Regex::new("^ +@([0-9]+)").unwrap());
        static EDGE_REGEX: Lazy<Regex> =
            Lazy::new(|| Regex::new("^ +([0-9]+) (-?[0-9]+) ([RF])").unwrap());
        let mut reference_time: u64 = 0;
        let mut events = Vec::new();
        loop {
            let mut more_data = false;
            let mut buffer_overrun = false;
            let mut unexpected_output = false;
            self.console.execute_command(
                &format!("gpio monitoring read {}", pin_names.join(" ")),
                |line| {
                    if let Some(captures) = START_TIME_REGEX.captures(line) {
                        reference_time = captures.get(1).unwrap().as_str().parse().unwrap();
                    } else if let Some(captures) = EDGE_REGEX.captures(line) {
                        events.push(MonitoringEvent {
                            signal_index: captures.get(1).unwrap().as_str().parse().unwrap(),
                            edge: if captures.get(3).unwrap().as_str() == "R" {
                                Edge::Rising
                            } else {
                                Edge::Falling
                            },
                            timestamp: (reference_time as i64
                                + captures.get(2).unwrap().as_str().parse::<i64>().unwrap())
                                as u64,
                        });
                    } else if line == "Warning: more data" {
                        more_data = true;
                    } else if line == "Error: Buffer overrun" {
                        buffer_overrun = true;
                    } else {
                        unexpected_output = true;
                        log::error!("Unexpected HyperDebug output: {}\n", line);
                    }
                },
            )?;
            if unexpected_output {
                bail!(TransportError::CommunicationError(
                    "Unrecognized response".to_string()
                ))
            }
            if buffer_overrun {
                bail!(TransportError::CommunicationError(
                    "HyperDebug GPIO monitoring buffer overrun".to_string()
                ))
            }
            if !more_data {
                break;
            }
        }
        if !continue_monitoring {
            self.console
                .cmd_no_output(&format!("gpio monitoring stop {}", pin_names.join(" ")))?;
        }
        Ok(MonitoringReadResponse {
            events,
            timestamp: reference_time,
        })
    }
}

/// Read 7 bits from each byte, least significant byte first.  High bit of one indicates more
/// bytes belong to the same value.
fn decode_leb128(idx: &mut usize, databytes: &[u8]) -> Result<u64> {
    let mut i = *idx;
    let mut value = 0u64;
    let mut shift = 0;
    while i < databytes.len() {
        let byte = databytes[i];
        value |= ((byte & 0x7F) as u64) << shift;
        shift += 7;
        i += 1;
        if (byte & 0x80) == 0 {
            *idx = i;
            return Ok(value);
        }
        if shift + 7 > 64 {
            // Too many bytes in encoding of a single integer, could overflow 64 bit unsigned.
            bail!(TransportError::CommunicationError(
                "Corrupt data from HyperDebug GPIO monitoring".to_string(),
            ));
        }
    }
    // End of stream "in the middle" of a multi-byte integer encoding.
    bail!(TransportError::CommunicationError(
        "Corrupt data from HyperDebug GPIO monitoring".to_string(),
    ));
}

pub struct HyperdebugGpioBitbanging {
    console: CommandHandler,
    inner: Rc<Inner>,
    cmsis_interface: BulkInterface,
}

impl HyperdebugGpioBitbanging {
    /// CMSIS extension for HyperDebug GPIO.
    const CMSIS_DAP_CUSTOM_COMMAND_GPIO: u8 = 0x83;

    /// Sub-command for HyperDebug GPIO bitbanging.
    const GPIO_BITBANG: u8 = 0x10;
    const GPIO_BITBANG_STREAMING: u8 = 0x11;

    /// Device status (whether there is an ongoing bitbang operation)
    const STATUS_BITBANG_IDLE: u8 = 0x00;
    const STATUS_BITBANG_ONGOING: u8 = 0x01;
    const STATUS_BITBANG_ERROR_WAVEFORM: u8 = 0x80;

    pub fn open(
        console: &CommandHandler,
        inner: &Rc<Inner>,
        cmsis_interface: BulkInterface,
    ) -> Result<Self> {
        // Exclusively claim CMSIS-DAP interface, preparing for bulk transfers.
        inner
            .usb_device
            .borrow_mut()
            .claim_interface(cmsis_interface.interface)?;
        Ok(Self {
            console: console.clone(),
            inner: Rc::clone(inner),
            cmsis_interface,
        })
    }
}

impl GpioBitbanging for HyperdebugGpioBitbanging {
    fn run(
        &self,
        pins: &[&dyn GpioPin],
        clock_tick: Duration,
        waveform: &mut [BitbangEntry],
    ) -> Result<()> {
        // Verify that `waveform` is valid, by converting into the binary representation to send
        // to HyperDebug.
        let mut encoded_waveform = encode_waveform(waveform, pins.len())?;

        // Tell HyperDebug about the set of pins to manipulate, and the clock speed, using the
        // textual console protocol.
        let mut pin_names = Vec::new();
        for pin in pins {
            pin_names.push(
                pin.get_internal_pin_name()
                    .ok_or(TransportError::InvalidOperation)?,
            );
        }
        self.console.cmd_no_output(&format!(
            "gpio bit-bang {} {}",
            clock_tick.as_nanos(),
            pin_names.join(" ")
        ))?;

        // Send an initial request, to ask how much buffer space HyperDebug has, so that we can
        // fill the buffer, while avoiding overflows.
        let usb = self.inner.usb_device.borrow();
        let mut free_bytes: usize = {
            let mut pkt = Vec::<u8>::new();
            pkt.write_u8(Self::CMSIS_DAP_CUSTOM_COMMAND_GPIO)?;
            pkt.write_u8(Self::GPIO_BITBANG)?;
            pkt.write_u16::<LittleEndian>(0)?;
            usb.write_bulk(self.cmsis_interface.out_endpoint, &pkt)?;

            let mut databytes = [0u8; 64];

            let c = usb.read_bulk(self.cmsis_interface.in_endpoint, &mut databytes)?;
            let mut rdr = Cursor::new(&databytes[..c]);
            ensure!(
                rdr.read_u8()? == Self::CMSIS_DAP_CUSTOM_COMMAND_GPIO,
                TransportError::CommunicationError(
                    "Incorrect CMSIS-DAP header in response to GPIO request".to_string()
                )
            );
            ensure!(
                rdr.read_u8()? == Self::STATUS_BITBANG_IDLE,
                TransportError::CommunicationError(
                    "HyperDebug not responding correctly".to_string()
                )
            );
            let free_bytes = rdr.read_u16::<LittleEndian>()?;
            free_bytes as usize
        };

        // Here is the main two-way transfer logic.  At each iteration we send a number of bytes,
        // capped at what HyperDebug has most recently indicated was available.  In response we
        // will receive some number of bytes of samples taken as the data was clocked out (similar
        // to how FTDI synchronous bitbanging works).  HyperDebug will send a response when it has
        // half of its buffer full of sampled data to send, or when some amount of time has passed
        // (relevant for slow clock speeds).  With this scheme, the bit-banging of waveforms
        // longer than what fits in HyperDebug memory can be produced, without HyperDebug ever
        // needing to "stop the clock" waiting for more data.
        let mut out_ptr = 0usize;
        let mut in_ptr = 0usize;
        while in_ptr < encoded_waveform.len() {
            let chunk_size = std::cmp::min(encoded_waveform.len() - out_ptr, free_bytes);

            let mut pkt = Vec::<u8>::new();
            pkt.write_u8(Self::CMSIS_DAP_CUSTOM_COMMAND_GPIO)?;
            if out_ptr + chunk_size < encoded_waveform.len() {
                // We prefer partial response, in order to be able to fill up buffer before
                // HyperDebug runs out of data to clock out.
                pkt.write_u8(Self::GPIO_BITBANG_STREAMING)?;
            } else {
                // We want response only after every byte is transmitted
                pkt.write_u8(Self::GPIO_BITBANG)?;
            }
            pkt.write_u16::<LittleEndian>(chunk_size as u16)?;
            pkt.extend_from_slice(&encoded_waveform[out_ptr..out_ptr + chunk_size]);
            usb.write_bulk(self.cmsis_interface.out_endpoint, &pkt)?;

            let mut databytes = [0u8; 64];

            let c = usb.read_bulk(self.cmsis_interface.in_endpoint, &mut databytes)?;
            let mut rdr = Cursor::new(&databytes[..c]);
            ensure!(
                rdr.read_u8()? == Self::CMSIS_DAP_CUSTOM_COMMAND_GPIO,
                TransportError::CommunicationError(
                    "Incorrect CMSIS-DAP header in response to GPIO request".to_string()
                )
            );
            match rdr.read_u8()? {
                Self::STATUS_BITBANG_ONGOING => (),
                Self::STATUS_BITBANG_IDLE => bail!(TransportError::CommunicationError(
                    "GPIO request aborted".to_string()
                )),
                Self::STATUS_BITBANG_ERROR_WAVEFORM => bail!(TransportError::CommunicationError(
                    "HyperDebug reports encoding error".to_string()
                )),
                status => bail!(TransportError::CommunicationError(std::format!(
                    "Unrecognized status code: {}",
                    status
                ))),
            }

            free_bytes = rdr.read_u16::<LittleEndian>()? as usize;
            let response_size = rdr.read_u16::<LittleEndian>()? as usize;

            let final_in_ptr = in_ptr + response_size;

            // Copy any data in initial packet
            let data_in_header = c - rdr.position() as usize;
            encoded_waveform[in_ptr..in_ptr + data_in_header]
                .copy_from_slice(&databytes[rdr.position() as usize..][..data_in_header]);
            in_ptr += data_in_header;

            while in_ptr < final_in_ptr {
                in_ptr += usb.read_bulk(
                    self.cmsis_interface.in_endpoint,
                    &mut encoded_waveform[in_ptr..final_in_ptr],
                )?;
            }

            out_ptr += chunk_size;
        }

        // Decode the binary representation from HyperDebug into any `BitbangEntry::Both()`
        // entries in `waveform`, allowing the caller to inspect data sampled at bitbanging clock
        // ticks (useful with open drain or pure input pins).
        decode_waveform(waveform, encoded_waveform, pins.len())?;

        Ok(())
    }
}

/// Produce binary encoding of waveform and delays, which can be sent to HyperDebug.
fn encode_waveform(waveform: &[BitbangEntry], num_pins: usize) -> Result<Vec<u8>> {
    ensure!(
        (1..=7).contains(&num_pins),
        GpioError::UnsupportedNumberOfPins(num_pins)
    );

    let mut encoded_waveform = Vec::<u8>::new();

    let mut delay = 0u32;
    for entry in waveform {
        match entry {
            BitbangEntry::Write(wbuf) | BitbangEntry::Both(wbuf, _) => {
                if delay > 1 {
                    // Delays are encoded using one or more bytes with the MSB set to one.  Each
                    // containing 7 bits of the delay value, with the least significant bits in
                    // the first byte.
                    let encoded_delay = delay - 1;
                    let mut shift = 0;
                    while (encoded_delay >> shift) != 0 {
                        encoded_waveform.push(0x80 | ((encoded_delay >> shift) & 0x7F) as u8);
                        shift += 7;
                    }
                }
                // A sequence of samples using up to 7 of the lowest bits, with the MSB set to
                // zero.
                for byte in *wbuf {
                    ensure!(
                        (byte >> num_pins) == 0,
                        GpioError::InvalidBitbangData(num_pins)
                    );
                }
                encoded_waveform.extend_from_slice(wbuf);
                delay = 0;
            }
            BitbangEntry::Delay(0) => bail!(GpioError::InvalidBitbangDelay),
            BitbangEntry::Delay(n @ 1..) => {
                delay += *n;
            }
        }
    }

    // Do not allow Delay as the final entry
    ensure!(delay == 0, GpioError::InvalidBitbangDelay);

    Ok(encoded_waveform)
}

/// Decode the binary representation from HyperDebug into any `BitbangEntry::Both()` entries in
/// `waveform`, allowing the caller to inspect data sampled at bitbanging clock ticks (useful with
/// open drain or pure input pins).
fn decode_waveform(
    waveform: &mut [BitbangEntry],
    encoded_response: Vec<u8>,
    num_pins: usize,
) -> Result<()> {
    ensure!(
        (1..=7).contains(&num_pins),
        GpioError::UnsupportedNumberOfPins(num_pins)
    );

    let mut index = 0usize;
    for entry in waveform {
        match entry {
            BitbangEntry::Write(wbuf) => {
                index += wbuf.len();
            }
            BitbangEntry::Both(wbuf, rbuf) => {
                ensure!(
                    rbuf.len() == wbuf.len(),
                    GpioError::MismatchedDataLength(wbuf.len(), rbuf.len())
                );
                rbuf.copy_from_slice(&encoded_response[index..][..rbuf.len()]);
                index += wbuf.len();
            }
            BitbangEntry::Delay(_) => {
                while encoded_response[index] & 0x80 != 0 {
                    index += 1;
                }
            }
        }
    }

    assert!(index == encoded_response.len());

    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_encode_waveforms() {
        let encoding = encode_waveform(
            &[
                BitbangEntry::Write(&[0, 1, 0, 1]),
                BitbangEntry::Delay(0x0101),
                BitbangEntry::Write(&[0, 1, 0, 1]),
            ],
            1,
        )
        .unwrap();

        assert_eq!(
            encoding,
            [0x00, 0x01, 0x00, 0x01, 0x80, 0x82, 0x00, 0x01, 0x00, 0x01]
        );
    }
}
