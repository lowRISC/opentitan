use anyhow::Result;
use std::io::{Read, Write};
use std::time::Duration;

/// A trait which represents a UART.
pub trait Uart: Read + Write {
    /// Returns the UART baudrate.  May return zero for virtual UARTs.
    fn get_baudrate(&self) -> u32;

    /// Sets the UART baudrate.  May do nothing for virtual UARTs.
    fn set_baudrate(&mut self, baudrate: u32) -> Result<()>;

    /// Reads UART recieve data into `buf`, returning the number of bytes read.
    /// The `timeout` may be used to specify a duration to wait for data.
    fn read_timeout(&mut self, buf: &mut [u8], timeout: Duration) -> Result<usize>;
}
