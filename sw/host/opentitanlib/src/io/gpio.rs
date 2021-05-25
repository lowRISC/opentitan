use anyhow::Result;

/// A trait which represents a GPIO interface.
pub trait Gpio {
    /// Reads the value of the the GPIO pin `id`.
    fn read(&self, id: usize) -> Result<bool>;

    /// Sets the value of the GPIO pin `id` to `value`.
    fn write(&self, id: usize, value: bool) -> Result<()>;
}
