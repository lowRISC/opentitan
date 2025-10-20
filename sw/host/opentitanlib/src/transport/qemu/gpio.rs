// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use std::cell::{Cell, RefCell};
use std::collections::HashMap;
use std::io::{BufRead, BufReader, Write};
use std::path::Path;
use std::rc::Rc;

use anyhow::{Context, bail};
use serialport::{SerialPort, TTYPort};

use crate::io::gpio::{GpioPin, PinMode, PullMode};

const QEMU_GPIO_CLEAR: char = 'C';
const QEMU_GPIO_DIRECTION: char = 'D';
const QEMU_GPIO_OUTPUT: char = 'O';
const QEMU_GPIO_PULL: char = 'P';
const QEMU_GPIO_QUERY: char = 'Q';
const QEMU_GPIO_FLOATING: char = 'Z';
const QEMU_GPIO_INPUT: char = 'I';
const QEMU_GPIO_MASK: char = 'M';

pub struct QemuGpio {
    pty: BufReader<TTYPort>,
    pub pins: HashMap<u8, Rc<dyn GpioPin>>,

    /// Current outputs being driven from host to QEMU when pins are in an
    /// outputting mode (ignored for inputs).
    pub host_to_qemu: u32,

    /// Current mask of which host pins are connected to QEMU inputs.
    ///
    /// - 0 indicates QEMU should ignore this pin as a host -> device input.
    /// - 1 indicates QEMU should treat this pin as a host -> device input.
    pub host_output_enable: u32,

    /// Current outputs being driven from QEMU to host (if pin in output mode).
    pub qemu_to_host: u32,

    /// Last reported input/output directions from QEMU:
    ///
    /// - 0 indicates input into QEMU.
    /// - 1 indicates output from QEMU.
    pub qemu_outputting: u32,

    /// Last reported pull up/down from QEMU:
    ///
    /// - 0 indicates QEMU is pulling down.
    /// - 1 indicates QEMU is pulling up.
    pub qemu_pull: u32,

    /// Last reported high impedance mode from QEMU:
    ///
    /// - 0 indicates QEMU is pulling up/down (see `qemu_pull`).
    /// - 1 indicates the pins are floating (high impedance / HiZ).
    pub qemu_floating: u32,
}

impl QemuGpio {
    pub fn new<P: AsRef<Path>>(gpio_pty: P) -> anyhow::Result<Self> {
        let pty = serialport::new(gpio_pty.as_ref().to_str().unwrap(), 0)
            .open_native()
            .context("failed to open QEMU GPIO PTY")?;
        let pty = BufReader::new(pty);

        let qemu_gpio = QemuGpio {
            pty,
            pins: HashMap::default(),
            host_to_qemu: 0x0,
            host_output_enable: 0x0,
            qemu_to_host: 0x0,
            qemu_outputting: 0x0,
            qemu_pull: 0x0,
            qemu_floating: 0x0,
        };

        Ok(qemu_gpio)
    }

    /// Process all GPIO command frames received from QEMU over the TTY.
    ///
    /// QEMU will send these when the state of the pins has changed in some way.
    /// Frames have the following format:
    ///
    /// ```
    /// <command>:<value>\r\n
    /// ```
    ///
    /// where `<command>` is a single uppercase character and `<value>` is four
    /// uppercase hex characters forming a value. This is a custom protocol for
    /// OpenTitan's QEMU machine.
    pub fn process_frames(&mut self) -> anyhow::Result<()> {
        while self.pty.get_ref().bytes_to_read()? > 0 {
            let mut line = String::new();
            self.pty
                .read_line(&mut line)
                .context("failed to read TTY")?;

            let (cmd, value) = line
                .split_once(":")
                .context("bad QEMU GPIO frame: missing ':'")?;
            let (cmd, value) = (cmd.trim(), value.trim());

            let &[cmd] = cmd.as_bytes() else {
                bail!("bad QEMU GPIO frame: expected single ascii char command, got {cmd}");
            };

            let value = u32::from_str_radix(value, 16).with_context(|| {
                format!("bad QEMU GPIO frame: expected four-hex value, got {value}")
            })?;

            match cmd as char {
                // QEMU wants us to clear / reset what we know about its pins.
                QEMU_GPIO_CLEAR => {
                    self.qemu_to_host = 0;
                    self.qemu_outputting = 0;
                    self.qemu_pull = 0;
                    self.qemu_floating = 0;
                }
                // The direction of one or more pins has changed between input/output.
                QEMU_GPIO_DIRECTION => self.qemu_outputting = value,
                // The output of one or more pins has changed.
                QEMU_GPIO_OUTPUT => self.qemu_to_host = value,
                // The pull up/down of one or more pins has changed.
                QEMU_GPIO_PULL => self.qemu_pull = value,
                // QEMU is querying our inputs to its pins.
                QEMU_GPIO_QUERY => {
                    self.send_frame(QEMU_GPIO_MASK, self.host_to_qemu)?;
                    self.send_frame(QEMU_GPIO_INPUT, self.host_to_qemu)?;
                }
                // The hi-Z value of one or more pins has changed.
                QEMU_GPIO_FLOATING => self.qemu_floating = value,
                _ => bail!("unknown command from QEMU: {cmd}"),
            }
        }

        Ok(())
    }

    /// Send a GPIO command frame to QEMU telling it about how we're driving the pins.
    ///
    /// See [`process_frames`] for a description of the frame format.
    ///
    /// Frame commands currently supported by QEMU are:
    ///
    /// * `I:<value>`:  the inputs to the device's pads are now `<value>`, if driven.
    /// * `M:<value>`:  the inputs are masked with `<value>`, meaning driven/connected.
    /// * `R:00000000`: ask QEMU to repeat the last `D` and `O` frames (see [`process_frames`]).
    pub fn send_frame(&mut self, cmd: char, value: u32) -> anyhow::Result<()> {
        writeln!(self.pty.get_mut(), "{cmd}:{value:08x}").context("failed to send GPIO frame")?;

        Ok(())
    }
}

pub struct QemuGpioPin {
    qemu_gpio: Rc<RefCell<QemuGpio>>,
    idx: u8,

    mode: Cell<PinMode>,

    /// Pull mode of the current pin.
    ///
    /// NOTE: QEMU does not currently support pulling the pin from the host
    /// side. We could attempt to emulate pulling by driving the output from
    /// our side, but we cannot model our pull being weaker than QEMU's driven
    /// output. For now we do not model pulling.
    pull_mode: Cell<PullMode>,
}

impl QemuGpioPin {
    pub(crate) fn new(qemu_gpio: Rc<RefCell<QemuGpio>>, idx: u8) -> Rc<Self> {
        let pin = QemuGpioPin {
            qemu_gpio,
            idx,
            mode: Cell::new(PinMode::Input),
            pull_mode: Cell::new(PullMode::None),
        };
        Rc::new(pin)
    }
}

impl GpioPin for QemuGpioPin {
    fn read(&self) -> anyhow::Result<bool> {
        if [PinMode::PushPull, PinMode::AnalogOutput].contains(&self.mode.get()) {
            log::warn!("attempting to read from output pin {}", self.idx);
        }

        let mut gpio = self.qemu_gpio.borrow_mut();

        gpio.process_frames()?;

        let qemu_outputting = (gpio.qemu_outputting >> self.idx & 1) == 1;

        let value = match qemu_outputting {
            true => gpio.qemu_to_host >> self.idx & 1,
            // For now we just give the pullup value regardless of whether it's floating.
            false => {
                let qemu_floating = (gpio.qemu_floating >> self.idx & 1) == 1;
                if qemu_floating {
                    log::warn!("attempted to read floating GPIO {}", self.idx);
                }
                gpio.qemu_pull >> self.idx & 1
            }
        };

        Ok(value == 1)
    }

    fn write(&self, value: bool) -> anyhow::Result<()> {
        let mut gpio = self.qemu_gpio.borrow_mut();
        let mut new_value = gpio.host_to_qemu;

        let mask = 1 << self.idx;
        if value {
            new_value |= mask;
        } else {
            new_value &= !mask;
        }

        if new_value != gpio.host_to_qemu {
            gpio.send_frame(QEMU_GPIO_INPUT, new_value)?;
            gpio.host_to_qemu = new_value;
        }

        Ok(())
    }

    fn set_mode(&self, mode: PinMode) -> anyhow::Result<()> {
        let mut gpio = self.qemu_gpio.borrow_mut();
        let mut new_value = gpio.host_output_enable;

        let mask = 1 << self.idx;
        if [PinMode::PushPull, PinMode::OpenDrain, PinMode::AnalogOutput].contains(&mode) {
            new_value |= mask;
        } else {
            new_value &= !mask;
        }

        if new_value != gpio.host_output_enable {
            // Note: the protocol inverts this mask so that `1` means ignored
            // and `0` means connected.
            gpio.send_frame(QEMU_GPIO_MASK, !new_value)?;
            gpio.host_output_enable = new_value;
        }

        self.mode.set(mode);

        Ok(())
    }

    fn set_pull_mode(&self, mode: PullMode) -> anyhow::Result<()> {
        // Currently ignored, see [`QemuGpioPin::pull_mode`].
        self.pull_mode.set(mode);

        Ok(())
    }

    fn set(
        &self,
        mode: Option<PinMode>,
        value: Option<bool>,
        pull: Option<PullMode>,
        analog_value: Option<f32>,
    ) -> anyhow::Result<()> {
        if let Some(mode) = mode {
            self.set_mode(mode)?;
        }

        if let Some(value) = value {
            self.write(value)?;
        }

        if let Some(pull) = pull {
            self.set_pull_mode(pull)?;
        }

        if let Some(_analog_value) = analog_value {
            todo!("QEMU transport does not yet support analogue GPIOs");
        }

        Ok(())
    }
}
