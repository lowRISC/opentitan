// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

pub mod monitor;
pub mod reset;

use std::cell::RefCell;
use std::rc::Rc;
use std::str::FromStr;

use anyhow::{bail, Context};

use crate::backend::qemu::QemuOpts;
use crate::io::gpio::{GpioError, GpioPin};
use crate::io::uart::Uart;
use crate::transport::common::uart::SerialPortUart;
use crate::transport::qemu::monitor::{Chardev, ChardevKind, Monitor};
use crate::transport::qemu::reset::QemuReset;
use crate::transport::{
    Capabilities, Capability, Transport, TransportError, TransportInterfaceType,
};

/// ID of the fake pin we use to model resets.
const QEMU_RESET_PIN_IDX: u8 = u8::MAX;

/// Represents a connection to a running QEMU emulation.
pub struct Qemu {
    /// Connection to the QEMU monitor which can control the emulator.
    pub monitor: Rc<RefCell<Monitor>>,

    /// Reset pin (actually goes via the `monitor`).
    reset: Rc<dyn GpioPin>,

    /// Console UART.
    console: Option<Rc<dyn Uart>>,

    /// QEMU log modelled as a UART.
    log: Option<Rc<dyn Uart>>,

    /// Whether to quit QEMU when dropped.
    quit: bool,
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
        let mut monitor = Monitor::new(options.qemu_monitor_tty.unwrap())?;

        // Get list of configured chardevs from QEMU.
        let chardevs = monitor.query_chardevs()?;
        fn find_chardev<'a>(chardevs: &'a [Chardev], id: &str) -> Option<&'a ChardevKind> {
            chardevs
                .iter()
                .find_map(|c| (c.id == id).then_some(&c.kind))
        }

        // Console UART:
        let console = match find_chardev(&chardevs, "console") {
            Some(ChardevKind::Pty { path }) => {
                let uart: Rc<dyn Uart> = Rc::new(
                    SerialPortUart::open_pseudo(path.to_str().unwrap(), 0)
                        .context("failed to open QEMU console PTY")?,
                );
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
                    SerialPortUart::open_pseudo(path.to_str().unwrap(), 0)
                        .context("failed to open QEMU log PTY")?,
                );
                Some(log)
            }
            _ => {
                log::info!("could not find pty chardev with id=log, skipping QEMU log");
                None
            }
        };

        let monitor = Rc::new(RefCell::new(monitor));

        // Resetting is done over the monitor, but we model it like a pin to enable strapping it.
        let reset = QemuReset::new(Rc::clone(&monitor));
        let reset = Rc::new(reset);

        Ok(Qemu {
            monitor,
            reset,
            console,
            log,
            quit: options.qemu_quit,
        })
    }
}

impl Drop for Qemu {
    fn drop(&mut self) {
        // Quit QEMU when dropped if requested.
        if self.quit {
            self.monitor.borrow_mut().quit().ok();
        }
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

        Ok(Capabilities::new(cap))
    }

    fn uart(&self, instance: &str) -> anyhow::Result<Rc<dyn Uart>> {
        match instance {
            "0" => Ok(Rc::clone(
                self.console.as_ref().context("uart 0 not connected")?,
            )),
            "log" => Ok(Rc::clone(
                self.log.as_ref().context("QEMU log not connected")?,
            )),
            _ => Err(TransportError::InvalidInstance(
                TransportInterfaceType::Uart,
                instance.to_string(),
            )
            .into()),
        }
    }

    fn gpio_pin(&self, instance: &str) -> anyhow::Result<Rc<dyn GpioPin>> {
        let pin = u8::from_str(instance).with_context(|| format!("can't convert {instance:?}"))?;

        if pin < 32 {
            bail!("GPIO interface not currently supported");
        } else if pin == QEMU_RESET_PIN_IDX {
            Ok(Rc::clone(&self.reset))
        } else {
            Err(GpioError::InvalidPinNumber(pin).into())
        }
    }
}
