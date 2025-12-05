// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

pub mod gpio;
pub mod i2c;
pub mod jtag;
pub mod monitor;
pub mod reset;
pub mod spi;
pub mod uart;
pub mod usbdev;

use std::cell::{Ref, RefCell};
use std::collections::HashMap;
use std::path::PathBuf;
use std::rc::Rc;
use std::str::FromStr;
use std::thread;
use std::time::Duration;

use anyhow::{Context, bail};

use crate::backend::qemu::QemuOpts;
use crate::io::gpio::{GpioError, GpioPin};
use crate::io::jtag::{JtagChain, JtagParams};
use crate::io::uart::Uart;
use crate::io::usb::UsbContext;
use crate::transport::Bus;
use crate::transport::Target;
use crate::transport::common::uart::SerialPortUart;
use crate::transport::qemu::gpio::{QemuGpio, QemuGpioPin};
use crate::transport::qemu::i2c::QemuI2c;
use crate::transport::qemu::jtag::QemuJtag;
use crate::transport::qemu::monitor::{Chardev, ChardevKind, Monitor};
use crate::transport::qemu::reset::QemuReset;
use crate::transport::qemu::spi::QemuSpi;
use crate::transport::qemu::uart::QemuUart;
use crate::transport::qemu::usbdev::{QemuUsbHost, QemuVbusSense};
use crate::transport::{
    Capabilities, Capability, Transport, TransportError, TransportInterfaceType,
};

/// ID of the fake pin we use to model resets.
const QEMU_RESET_PIN_IDX: u8 = u8::MAX;
/* Until we have a more complete model of the pinmux, we need to model this
 * MIO directly. */
const QEMU_VBUS_SENSE_PIN_IDX: u8 = u8::MAX - 1;

/// Baudrate for QEMU's consoles. These are PTYs so it currently doesn't matter,
/// but we must use a non-zero value because the pacing calculations divide by
/// this number.
const CONSOLE_BAUDRATE: u32 = 115200;

/// Represents a connection to a running QEMU emulation.
pub struct Qemu {
    /// Connection to the QEMU monitor which can control the emulator.
    pub monitor: Rc<RefCell<Monitor>>,

    /// Reset pin (actually goes via the `monitor`).
    reset: Rc<dyn GpioPin>,

    /// Console UART.
    uarts: HashMap<String, Rc<dyn Uart>>,

    /// SPI device.
    spi: Option<Rc<dyn Target>>,

    /// I2C devices.
    i2cs: HashMap<String, Rc<dyn Bus>>,

    /// GPIO pins (not including reset pin).
    gpio: Option<Rc<RefCell<QemuGpio>>>,

    /// VBUS sense pin (actually goes via the `usbdev-cmd` chardev).
    vbus_sense: Option<Rc<dyn GpioPin>>,

    /// USB host TTY port name (`usbdev-host` chardev).
    usb_host_tty: Option<String>,

    /// USB host.
    usb_host: RefCell<Option<Rc<dyn UsbContext>>>,

    /// QEMU log modelled as a UART.
    log: Option<Rc<dyn Uart>>,

    /// Debug module JTAG.
    jtag_rv_dm_sock: Option<PathBuf>,

    /// Lifecycle controller JTAG.
    jtag_lc_ctrl_sock: Option<PathBuf>,
}

impl Qemu {
    /// Creates a QEMU transport connection from `options`.
    ///
    /// The transport will configure capabilities that it can find from the running QEMU instance.
    /// It looks for the following chardevs which should be connected to QEMU devices:
    ///
    /// * `uart{n}` (pty) - connect to UARTs in order using `-serial chardev:uart{n}`.
    /// * `log`     (pty) - connect to QEMU's log using `-global ot-ibex_wrapper.logdev=log`.
    /// * `spidev`  (pty) - automatically connected to QEMU spi device.
    /// * `i2c{n}`  (pty) - connect to I2C bus using `-device ot-i2c_host_proxy,bus=ot-i2c{n},chardev=i2c{n}`.
    /// * `gpio`    (pty) - connect to GPIO block using `global ot-gpio-{eg,dj}.chardev=gpio`
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

        // UARTs:
        let mut uarts = HashMap::new();
        for chardev in &chardevs {
            let Some(id) = chardev.id.strip_prefix("uart") else {
                continue;
            };

            let ChardevKind::Pty { ref path } = chardev.kind else {
                continue;
            };

            let serial_port = SerialPortUart::open_pseudo(path.to_str().unwrap(), CONSOLE_BAUDRATE)
                .context("failed to open QEMU console PTY")?;
            let uart: Rc<dyn Uart> =
                Rc::new(QemuUart::new(Rc::clone(&monitor), &chardev.id, serial_port));

            uarts.insert(id.to_string(), uart);
        }
        if uarts.is_empty() {
            log::info!(
                "could not find pty chardevs with ids starting with `uart`, UART support disabled"
            );
        }

        // USBDEV control:
        let vbus_sense = match find_chardev(&chardevs, "usbdev-cmd") {
            Some(ChardevKind::Pty { path }) => {
                let tty = serialport::new(
                    path.to_str().context("TTY path not UTF8")?,
                    CONSOLE_BAUDRATE,
                )
                .open_native()
                .context("failed to open QEMU usbdev-cmd PTY")?;

                let vbus_sense: Rc<dyn GpioPin> = Rc::new(QemuVbusSense::new(tty));
                Some(vbus_sense)
            }
            _ => {
                log::info!("could not find pty chardev with id=usbdev, skipping USBDEV");
                None
            }
        };

        // USBDEV host:
        let usb_host_tty = match find_chardev(&chardevs, "usbdev-host") {
            Some(ChardevKind::Pty { path }) => {
                Some(path.to_str().context("TTY path not UTF8")?.to_string())
            }
            _ => {
                log::info!("could not find pty chardev with id=usbdev-host, skipping USBDEV");
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
                log::info!("could not find pty chardev with id=log, QEMU log unavailable");
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
                log::info!("could not find pty chardev with id=spidev, SPI support disabled");
                None
            }
        };

        // Try connecting to each of the I2C buses.
        let mut i2cs = HashMap::new();
        for chardev in &chardevs {
            let Some(id) = chardev.id.strip_prefix("i2c") else {
                continue;
            };

            let ChardevKind::Pty { ref path } = chardev.kind else {
                continue;
            };

            let i2c = QemuI2c::new(path).context("failed to connect to QEMU I2C PTY")?;
            let i2c: Rc<dyn Bus> = Rc::new(i2c);

            i2cs.insert(id.to_string(), i2c);
        }
        if i2cs.is_empty() {
            log::info!(
                "could not find pty chardevs with ids starting with `i2c`, I2C support disabled"
            );
        }

        // If there's a chardev called `gpio`, configure it as a PTY and use as the GPIO pins.
        let gpio = match find_chardev(&chardevs, "gpio") {
            Some(ChardevKind::Pty { path }) => {
                let gpio = QemuGpio::new(path).context("failed to connect to QEMU GPIO PTY")?;
                let gpio = Rc::new(RefCell::new(gpio));
                Some(gpio)
            }
            _ => {
                log::info!("could not find pty chardev with id=gpio, GPIO support disabled");
                None
            }
        };

        // Debug module JTAG tap:
        let jtag_rv_dm_sock = match find_chardev(&chardevs, "taprbb") {
            Some(ChardevKind::Socket { path }) => Some(path.clone()),
            _ => {
                log::info!("could not find socket chardev with id=taprbb, skipping RV_DM JTAG");
                None
            }
        };

        // Lifecycle controller JTAG tap:
        let jtag_lc_ctrl_sock = match find_chardev(&chardevs, "taprbb-lc-ctrl") {
            Some(ChardevKind::Socket { path }) => Some(path.clone()),
            _ => {
                log::info!(
                    "could not find socket chardev with id=taprbb-lc-ctrl, skipping LC JTAG"
                );
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
            uarts,
            vbus_sense,
            usb_host_tty,
            usb_host: RefCell::new(None),
            log,
            spi,
            i2cs,
            gpio,
            jtag_rv_dm_sock,
            jtag_lc_ctrl_sock,
        })
    }
}

impl Transport for Qemu {
    fn capabilities(&self) -> anyhow::Result<Capabilities> {
        // We have to unconditionally claim to support GPIO because of the reset
        // pin which actually goes via the monitor. Attempting to use a non-reset
        // GPIO pin in `.gpio_pin` will cause an error if GPIO isn't connected.
        let mut cap = Capability::GPIO;

        if !self.uarts.is_empty() || self.log.is_some() {
            cap |= Capability::UART;
        }

        if self.spi.is_some() {
            cap |= Capability::SPI;
        }

        if !self.i2cs.is_empty() {
            cap |= Capability::I2C;
        }

        if self.usb_host_tty.is_some() {
            cap |= Capability::USB;
        }

        Ok(Capabilities::new(cap))
    }

    fn uart(&self, instance: &str) -> anyhow::Result<Rc<dyn Uart>> {
        if instance == "LOG" {
            return Ok(Rc::clone(
                self.log.as_ref().context("QEMU log not connected")?,
            ));
        }

        match self.uarts.get(instance) {
            Some(uart) => Ok(Rc::clone(uart)),
            None => Err(TransportError::InvalidInstance(
                TransportInterfaceType::Uart,
                instance.to_string(),
            )
            .into()),
        }
    }

    fn i2c(&self, instance: &str) -> anyhow::Result<Rc<dyn Bus>> {
        match self.i2cs.get(instance) {
            Some(i2c) => Ok(Rc::clone(i2c)),
            None => Err(TransportError::InvalidInstance(
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
        } else if pin == QEMU_VBUS_SENSE_PIN_IDX && self.vbus_sense.is_some() {
            Ok(Rc::clone(self.vbus_sense.as_ref().unwrap()))
        } else {
            Err(GpioError::InvalidPinNumber(pin).into())
        }
    }

    fn spi(&self, _instance: &str) -> anyhow::Result<Rc<dyn Target>> {
        Ok(Rc::clone(self.spi.as_ref().unwrap()))
    }

    fn jtag(&self, opts: &JtagParams) -> anyhow::Result<Box<dyn JtagChain>> {
        let rv_dm_sock = self
            .jtag_rv_dm_sock
            .clone()
            .context("RV_DM JTAG socket not connected")?;
        let lc_ctrl_sock = self
            .jtag_lc_ctrl_sock
            .clone()
            .context("LC_CTRL JTAG socket not connected")?;

        let jtag = QemuJtag::new(opts.clone(), rv_dm_sock, lc_ctrl_sock);

        Ok(Box::new(jtag))
    }

    fn usb(&self) -> anyhow::Result<Rc<dyn UsbContext>> {
        if self.usb_host.borrow().is_none() {
            let tty = serialport::new(
                self.usb_host_tty
                    .as_ref()
                    .context("USB is not supported (no usbdev-host chardev found)")?,
                CONSOLE_BAUDRATE,
            )
            .open_native()
            .context("failed to open QEMU usbdev-host PTY")?;

            let usb_host: Rc<dyn UsbContext> = Rc::new(QemuUsbHost::new(tty));
            self.usb_host.replace(Some(usb_host));
        }
        let usb_host = self.usb_host.borrow();
        let usb_host = Ref::map(usb_host, |d| d.as_ref().expect("usb host"));
        Ok(usb_host.clone())
    }
}
