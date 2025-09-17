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

pub struct QemuGpio {
    tty: BufReader<TTYPort>,
    pub pins: HashMap<u8, Rc<dyn GpioPin>>,

    /// Current outputs being driven from host to QEMU (if pin in output mode).
    pub host_to_qemu: u32,

    /// Current mask of which host pins are connected to QEMU inputs, i.e. outputting.
    pub host_output_mask: u32,

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

    /// Last reported high impedence mode from QEMU:
    ///
    /// - 0 indicates QEMU is pulling up/down (see `qemu_pull`).
    /// - 1 indicates the pins are floating (high impedance / HiZ).
    pub qemu_floating: u32,
}

impl QemuGpio {
    pub fn new<P: AsRef<Path>>(gpio_tty: P) -> anyhow::Result<Self> {
        let tty = serialport::new(gpio_tty.as_ref().to_str().unwrap(), 0).open_native()?;
        let tty = BufReader::new(tty);

        let qemu_gpio = QemuGpio {
            tty,
            pins: HashMap::default(),
            host_to_qemu: 0,
            host_output_mask: u32::MAX,
            qemu_to_host: 0,
            qemu_outputting: 0,
            qemu_pull: 0,
            qemu_floating: 0,
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
    /// where `<command>` is a single uppercase character and `<value>` are four
    /// uppercase hex characters forming a value. This is a custom protocol for
    /// OpenTitan's QEMU machine.
    pub fn process_frames(&mut self) -> anyhow::Result<()> {
        while self.tty.get_ref().bytes_to_read()? > 0 {
            let mut line = String::new();
            self.tty
                .read_line(&mut line)
                .context("failed to read TTY")?;

            let (cmd, value) = line
                .split_once(":")
                .context("bad QEMU GPIO frame: missing ':'")?;
            let (cmd, value) = (cmd.trim(), value.trim());

            let value = u32::from_str_radix(value, 16).with_context(|| {
                format!("bad QEMU GPIO frame: expected four-hex value, got {value}")
            })?;

            match cmd {
                // QEMU wants us to Clear / reset what we know about its pins.
                "C" => {
                    self.qemu_to_host = 0;
                    self.qemu_outputting = 0;
                    self.qemu_pull = 0;
                    self.qemu_floating = 0;
                }
                // The Direction of one or more pins has changed between input/output.
                "D" => self.qemu_outputting = value,
                // The Output of one or more pins has changed.
                "O" => self.qemu_to_host = value,
                // The Pull up/down of one or more pins has changed.
                "P" => self.qemu_pull = value,
                // QEMU is Querying our inputs to its pins.
                "Q" => self.send_frame('I', self.host_to_qemu)?,
                // The hi-Z value of one or more pins has changed.
                "Z" => self.qemu_floating = value,
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
    /// * `I:<value>`: the Inputs to the device's pads are now `<value>`.
    /// * `M:<value>`: the inputs are Masked with `<value>`, meaning connected.
    /// * `R:00000000`:    ask QEMU to Repeat the last `d` and `o` frames (see [`process_frames`]).
    pub fn send_frame(&mut self, cmd: char, value: u32) -> anyhow::Result<()> {
        writeln!(self.tty.get_mut(), "{cmd}:{value:08x}").context("failed to send GPIO frame")?;

        Ok(())
    }
}

pub struct QemuGpioPin {
    qemu_gpio: Rc<RefCell<QemuGpio>>,
    idx: u8,

    mode: Cell<PinMode>,
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

    fn outputting(&self) -> bool {
        match self.mode.get() {
            PinMode::Input => false,
            PinMode::PushPull => true,
            PinMode::OpenDrain => true,
            PinMode::AnalogInput => false,
            PinMode::AnalogOutput => true,
            PinMode::Alternate => false,
        }
    }
}

impl GpioPin for QemuGpioPin {
    fn read(&self) -> anyhow::Result<bool> {
        if self.outputting() {
            log::warn!("attempting to read from output pin {}", self.idx);
        }

        let mut gpio = self.qemu_gpio.borrow_mut();

        gpio.process_frames()?;

        let qemu_outputting = (gpio.qemu_outputting >> self.idx & 1) == 1;
        let value = match qemu_outputting {
            true => gpio.qemu_to_host >> self.idx & 1,
            // For now we just give the pullup value regardless of whether it's floating.
            false => gpio.qemu_pull >> self.idx & 1,
        };

        Ok(value == 1)
    }

    fn write(&self, value: bool) -> anyhow::Result<()> {
        if !self.outputting() {
            log::warn!(
                "write to pin {} will not be visible until mode changes to an output",
                self.idx
            );
        }

        let mut gpio = self.qemu_gpio.borrow_mut();

        let mask = 1 << self.idx;
        if value {
            gpio.host_to_qemu |= mask;
        } else {
            gpio.host_to_qemu &= !mask;
        }

        let value = gpio.host_to_qemu;
        gpio.send_frame('I', value)?;

        Ok(())
    }

    fn set_mode(&self, mode: PinMode) -> anyhow::Result<()> {
        self.mode.set(mode);

        let mut gpio = self.qemu_gpio.borrow_mut();
        let mask = 1 << self.idx;
        if self.outputting() {
            gpio.host_output_mask &= !mask;
        } else {
            gpio.host_output_mask |= mask;
        }

        let output_mask = gpio.host_output_mask;
        gpio.send_frame('M', output_mask)?;

        Ok(())
    }

    fn set_pull_mode(&self, mode: PullMode) -> anyhow::Result<()> {
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
