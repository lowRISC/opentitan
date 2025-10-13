// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

pub mod gpio;
pub mod i2c;
pub mod monitor;
pub mod reset;
pub mod spi;
pub mod uart;

use std::cell::RefCell;
use std::rc::Rc;
use std::str::FromStr;
use std::thread;
use std::time::Duration;

use anyhow::{Context, bail};

use crate::backend::qemu::QemuOpts;
use crate::io::gpio::{GpioError, GpioPin};
use crate::io::uart::Uart;
use crate::transport::Bus;
use crate::transport::Target;
use crate::transport::common::uart::SerialPortUart;
use crate::transport::qemu::gpio::{QemuGpio, QemuGpioPin};
use crate::transport::qemu::i2c::QemuI2c;
use crate::transport::qemu::monitor::{Chardev, ChardevKind, Monitor};
use crate::transport::qemu::reset::QemuReset;
use crate::transport::qemu::spi::QemuSpi;
use crate::transport::qemu::uart::QemuUart;
use crate::transport::{
    Capabilities, Capability, Transport, TransportError, TransportInterfaceType,
};

/// ID of the fake pin we use to model resets.
const QEMU_RESET_PIN_IDX: u8 = u8::MAX;

/// Baudrate for QEMU's consoles. These are PTYs so it currently doesn't matter,
/// but we must use a non-zero value because the pacing calculations divide by
/// this number.
const CONSOLE_BAUDRATE: u32 = 115200;

/// Number of I2Cs.
const NUM_I2CS: usize = 3;

/// Represents a connection to a running QEMU emulation.
pub struct Qemu {
    /// Connection to the QEMU monitor which can control the emulator.
    pub monitor: Rc<RefCell<Monitor>>,

    /// Reset pin (actually goes via the `monitor`).
    reset: Rc<dyn GpioPin>,

    /// Console UART.
    console: Option<Rc<dyn Uart>>,

    /// SPI device.
    spi: Option<Rc<dyn Target>>,

    /// I2C devices.
    i2cs: [Option<Rc<dyn Bus>>; NUM_I2CS],

    /// GPIO pins (not including reset pin).
    gpio: Option<Rc<RefCell<QemuGpio>>>,

    /// QEMU log modelled as a UART.
    log: Option<Rc<dyn Uart>>,
}

impl Qemu {
    /// Creates a QEMU transport connection from `options`.
    ///
    /// The transport will configure capabilities that it can find from the running QEMU instance.
    /// It looks for the following chardevs which should be connected to QEMU devices:
    ///
    /// * `console` (pty) - connect to UART using `-serial chardev:console`.
    /// * `log`     (pty) - connect to QEMU's log using `-global ot-ibex_wrapper.logdev=log`.
    ///
    /// You can create a chardev with `-chardev <kind>,id=<id>` and connect it
    /// to a device using one of the flags in the list above. The kind must
    /// match what OpenTitanLib expects to be accepted.
    pub fn from_options(options: QemuOpts) -> anyhow::Result<Self> {
        let monitor = Rc::new(RefCell::new(Monitor::new(
            options.qemu_monitor_tty.unwrap(),
            options.qemu_quit,
        )?));

        // Get list of configured chardevs from QEMU.
        let chardevs = monitor.borrow_mut().query_chardevs()?;
        fn find_chardev<'a>(chardevs: &'a [Chardev], id: &str) -> Option<&'a ChardevKind> {
            chardevs
                .iter()
                .find_map(|c| (c.id == id).then_some(&c.kind))
        }

        // Console UART:
        let console = match find_chardev(&chardevs, "console") {
            Some(ChardevKind::Pty { path }) => {
                let serial_port =
                    SerialPortUart::open_pseudo(path.to_str().unwrap(), CONSOLE_BAUDRATE)
                        .context("failed to open QEMU console PTY")?;
                let uart: Rc<dyn Uart> =
                    Rc::new(QemuUart::new(Rc::clone(&monitor), "console", serial_port));
                Some(uart)
            }
            _ => {
                log::info!("could not find pty chardev with id=console, skipping UART");
                None
            }
        };

        // QEMU log, not really a UART but modelled as one:
        let log = match find_chardev(&chardevs, "log") {
            Some(ChardevKind::Pty { path }) => {
                let log: Rc<dyn Uart> = Rc::new(
                    SerialPortUart::open_pseudo(path.to_str().unwrap(), CONSOLE_BAUDRATE)
                        .context("failed to open QEMU log PTY")?,
                );
                Some(log)
            }
            _ => {
                log::info!("could not find pty chardev with id=log, skipping QEMU log");
                None
            }
        };

        // If there's a chardev called `spidev`, configure it as a PTY and use as the SPI bus.
        let spi = match find_chardev(&chardevs, "spidev") {
            Some(ChardevKind::Pty { path }) => {
                let spi = QemuSpi::new(path).context("failed to connect to QEMU SPI PTY")?;
                let spi: Rc<dyn Target> = Rc::new(spi);
                Some(spi)
            }
            _ => {
                log::info!("could not find pty chardev with id=spidev, skipping SPI");
                None
            }
        };

        // Try connecting to each of the I2C buses.
        let mut i2cs = [const { None }; NUM_I2CS];
        for (idx, i2cn) in i2cs.iter_mut().enumerate() {
            let chardev_id = format!("i2c{}", idx);
            *i2cn = match find_chardev(&chardevs, &chardev_id) {
                Some(ChardevKind::Pty { path }) => {
                    let i2c = QemuI2c::new(path).context("failed to connect to QEMU I2C PTY")?;
                    let i2c: Rc<dyn Bus> = Rc::new(i2c);
                    Some(i2c)
                }
                _ => {
                    log::info!(
                        "could not find pty chardev with id={}, skipping this I2C bus",
                        &chardev_id
                    );
                    None
                }
            };
        }

        // If there's a chardev called `gpio`, configure it as a PTY and use as the GPIO pins.
        let gpio = match find_chardev(&chardevs, "gpio") {
            Some(ChardevKind::Pty { path }) => {
                let gpio = QemuGpio::new(path).context("failed to connect to QEMU GPIO PTY")?;
                let gpio = Rc::new(RefCell::new(gpio));
                Some(gpio)
            }
            _ => {
                log::info!("could not find pty chardev with id=gpio, skipping GPIO");
                None
            }
        };

        // Resetting is done over the monitor, but we model it like a pin to enable strapping it.
        let reset = QemuReset::new(Rc::clone(&monitor));
        let reset = Rc::new(reset);

        // QEMU polls once per second to see if PTYs have been connected to. We must wait that
        // full second to be sure that QEMU is watching all of them.
        thread::sleep(Duration::from_secs(1));

        Ok(Qemu {
            monitor,
            reset,
            console,
            log,
            spi,
            i2cs,
            gpio,
        })
    }
}

impl Transport for Qemu {
    fn capabilities(&self) -> anyhow::Result<Capabilities> {
        // We have to unconditionally claim to support GPIO because of the reset
        // pin which actually goes via the monitor. Attempting to use a non-reset
        // GPIO pin in `.gpio_pin` will cause an error if GPIO isn't connected.
        let mut cap = Capability::GPIO;

        if self.console.is_some() || self.log.is_some() {
            cap |= Capability::UART;
        }

        if self.spi.is_some() {
            cap |= Capability::SPI;
        }

        Ok(Capabilities::new(cap))
    }

    fn uart(&self, instance: &str) -> anyhow::Result<Rc<dyn Uart>> {
        match instance {
            "0" => Ok(Rc::clone(
                self.console.as_ref().context("uart 0 not connected")?,
            )),
            "LOG" => Ok(Rc::clone(
                self.log.as_ref().context("QEMU log not connected")?,
            )),
            _ => Err(TransportError::InvalidInstance(
                TransportInterfaceType::Uart,
                instance.to_string(),
            )
            .into()),
        }
    }

    fn i2c(&self, instance: &str) -> anyhow::Result<Rc<dyn Bus>> {
        match instance {
            "0" => Ok(Rc::clone(
                self.i2cs[0].as_ref().context("QEMU I2C 0 not connected")?,
            )),
            "1" => Ok(Rc::clone(
                self.i2cs[1].as_ref().context("QEMU I2C 1 not connected")?,
            )),
            "2" => Ok(Rc::clone(
                self.i2cs[2].as_ref().context("QEMU I2C 2 not connected")?,
            )),
            _ => Err(TransportError::InvalidInstance(
                TransportInterfaceType::I2c,
                instance.to_string(),
            )
            .into()),
        }
    }

    fn gpio_pin(&self, instance: &str) -> anyhow::Result<Rc<dyn GpioPin>> {
        let pin = u8::from_str(instance).with_context(|| format!("can't convert {instance:?}"))?;

        if pin < 32 {
            let Some(ref gpio) = self.gpio else {
                bail!("GPIO interface not connected");
            };

            let mut gpio = gpio.borrow_mut();
            let gpio = gpio
                .pins
                .entry(pin)
                .or_insert_with(|| QemuGpioPin::new(Rc::clone(self.gpio.as_ref().unwrap()), pin));

            Ok(Rc::clone(gpio))
        } else if pin == QEMU_RESET_PIN_IDX {
            Ok(Rc::clone(&self.reset))
        } else {
            Err(GpioError::InvalidPinNumber(pin).into())
        }
    }

    fn spi(&self, _instance: &str) -> anyhow::Result<Rc<dyn Target>> {
        Ok(Rc::clone(self.spi.as_ref().unwrap()))
    }
}
