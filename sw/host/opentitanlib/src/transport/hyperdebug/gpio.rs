use anyhow::Result;

use crate::io::gpio::{Gpio, PinDirection, StrapConfig};
use crate::transport::hyperdebug::Hyperdebug;

pub struct HyperdebugGpio {
    console_tty: Box<std::path::Path>,
    _gpio_names: Vec<String>, // TODO(jbk): Should probably be reference, rather than copy
}

impl HyperdebugGpio {
    pub fn open(hyperdebug: &Hyperdebug) -> Result<Self> {
        let result = HyperdebugGpio {
            console_tty: hyperdebug.console_tty.clone(),
            _gpio_names: hyperdebug.gpio_names.clone(),
        };
        Ok(result)
    }
}

impl Gpio for HyperdebugGpio {
    /// Reads the value of the the GPIO pin `id`.
    fn read(&self, _id: &str) -> Result<bool> {
        Ok(false)
    }

    /// Sets the value of the GPIO pin `id` to `value`.
    fn write(&self, id: &str, value: bool) -> Result<()> {
        Hyperdebug::execute_command(
            &self.console_tty,
            &format!("gpioset {} {}", id, if value { 1 } else { 0 }),
            |_| {})
    }

    /// Sets the `direction` of GPIO `id` as input or output.
    fn set_direction(&self, _id: &str, _direction: PinDirection) -> Result<()> {
        unimplemented!()
    }

    /// Drive the reset pin. The `reset` parameter represents whether or not the caller
    /// wants to drive the chip into reset, _not_ the logic-level of the reset pin.
    fn drive_reset(&self, _reset: bool) -> Result<()> {
        unimplemented!()
    }

    /// Set the requested strap value to the strapping pins.  Note: not all backends
    /// support all settings.  An unsupported StrapConfig will result in an
    /// `InvalidStrapConfig` error.
    fn set_strap_pins(&self, _strap: StrapConfig) -> Result<()> {
        unimplemented!()
    }
}
