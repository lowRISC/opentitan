use anyhow::Result;
use regex::Regex;
use std::fs::File;
use std::fs::OpenOptions;
use std::io::{Read, Write};
use std::ops::Drop;
use std::process::{Child, ChildStdout, Command, Stdio};
use std::time::{Duration, Instant};

use crate::io::uart::Uart;
use crate::transport::{Capabilities, Capability, Transport};
use crate::util::file;

/// Verilator startup options.
pub struct Options {
    /// The verilator executable.
    pub executable: String,
    /// The ROM image used to boot the CPU.
    pub rom_image: String,
    /// The flash image stored in internal flash memory.
    pub flash_image: String,
    /// The OTP settings.
    pub otp_image: String,
    /// Any extra arguments to verilator.
    pub extra_args: Vec<String>,
}

struct Subprocess {
    child: Child,
    stdout: ChildStdout,
    accumulated_output: String,
}

impl Subprocess {
    /// Starts a verilator [`Subprocess`] based on [`Options`].
    fn from_options(options: Options) -> Result<Self> {
        let mut command = Command::new(&options.executable);
        let mut args = Vec::new();

        if !options.rom_image.is_empty() {
            args.push(format!("--meminit=rom,{}", options.rom_image));
        }
        if !options.flash_image.is_empty() {
            args.push(format!("--meminit=flash,{}", options.flash_image));
        }
        if !options.otp_image.is_empty() {
            args.push(format!("--meminit=otp,{}", options.otp_image));
        }
        args.extend_from_slice(&options.extra_args[..]);
        command.args(&args[..]);

        info!("Spawning verilator: {:?} {:?}", options.executable, args);

        let mut child = command
            .stdin(Stdio::null())
            .stdout(Stdio::piped())
            .stderr(Stdio::inherit())
            .spawn()?;
        let stdout = child.stdout.take().unwrap();
        Ok(Subprocess {
            child: child,
            stdout: stdout,
            accumulated_output: String::default(),
        })
    }

    /// Accumulates output from verilator's `stdout`.
    fn accumulate(&mut self, timeout: Duration) -> Result<()> {
        let mut buf = [0u8; 256];
        file::wait_read_timeout(&self.stdout, timeout)?;
        let n = self.stdout.read(&mut buf)?;
        let s = String::from_utf8_lossy(&buf[..n]);
        self.accumulated_output.push_str(&s);
        Ok(())
    }

    /// Finds a string within the verilator output.
    /// It is assumed that the [`Regex`] `re` has exactly one capture.
    fn find(&mut self, re: &Regex, timeout: Duration) -> Result<String> {
        let deadline = Instant::now() + timeout;
        loop {
            if let Some(captures) = re.captures(&self.accumulated_output) {
                let val = captures.get(1).expect("expected a capture");
                return Ok(val.as_str().to_owned());
            } else {
                let delta = deadline - Instant::now();
                self.accumulate(delta)?;
            }
        }
    }

    /// Kill the verilator subprocess.
    fn kill(&mut self) -> Result<()> {
        self.child.kill()?;
        Ok(())
    }
}

/// Represents the verilator transport object.
pub struct Verilator {
    subprocess: Option<Subprocess>,
    pub uart_file: String,
    pub spi_file: String,
    pub gpio_read_file: String,
    pub gpio_write_file: String,
}

impl Verilator {
    /// Creates a verilator subprocess-hosting transport from [`options`].
    pub fn from_options(options: Options) -> Result<Self> {
        lazy_static! {
            static ref UART: Regex = Regex::new("UART: Created ([^ ]+) for uart0").unwrap();
            static ref SPI: Regex = Regex::new("SPI: Created ([^ ]+) for spi0").unwrap();
            static ref GPIO_RD: Regex =
                Regex::new(r#"GPIO: FIFO pipes created at ([^ ]+) \(read\) and [^ ]+ \(write\) for 32-bit wide GPIO."#).unwrap();
            static ref GPIO_WR: Regex =
                Regex::new(r#"GPIO: FIFO pipes created at [^ ]+ \(read\) and ([^ ]+) \(write\) for 32-bit wide GPIO."#).unwrap();
        }

        let mut subprocess = Subprocess::from_options(options)?;
        let gpio_rd = subprocess.find(&GPIO_RD, Duration::from_secs(5))?;
        let gpio_wr = subprocess.find(&GPIO_WR, Duration::from_secs(5))?;
        let uart = subprocess.find(&UART, Duration::from_secs(5))?;
        let spi = subprocess.find(&SPI, Duration::from_secs(5))?;

        info!("Verilator started with the following interaces:");
        info!("gpio_read = {}", gpio_rd);
        info!("gpio_write = {}", gpio_wr);
        info!("uart = {}", uart);
        info!("spi = {}", spi);
        Ok(Verilator {
            subprocess: Some(subprocess),
            uart_file: uart,
            spi_file: spi,
            gpio_read_file: gpio_rd,
            gpio_write_file: gpio_wr,
        })
    }

    /// Shuts down the verilator subprocess.
    pub fn shutdown(&mut self) -> Result<()> {
        if let Some(mut subprocess) = self.subprocess.take() {
            subprocess.kill()
        } else {
            Ok(())
        }
    }
}

impl Drop for Verilator {
    fn drop(&mut self) {
        self.shutdown().expect("Kill verilator subprocess");
    }
}

impl Transport for Verilator {
    fn capabilities(&self) -> Capabilities {
        Capabilities::new(Capability::UART)
    }

    fn uart(&self) -> Result<Box<dyn Uart>> {
        Ok(Box::new(VerilatorUart::open(&self.uart_file)?))
    }
}

/// Represents the verilator virtual UART.
struct VerilatorUart {
    file: File,
}

impl VerilatorUart {
    pub fn open(path: &str) -> Result<Self> {
        let file = OpenOptions::new().read(true).write(true).open(path)?;
        Ok(VerilatorUart { file: file })
    }
}

impl Uart for VerilatorUart {
    fn get_baudrate(&self) -> u32 {
        7200
    }
    fn set_baudrate(&mut self, _baudrate: u32) -> Result<()> {
        Ok(())
    }

    fn read_timeout(&mut self, buf: &mut [u8], timeout: Duration) -> Result<usize> {
        file::wait_read_timeout(&self.file, timeout)?;
        let n = self.file.read(buf)?;
        Ok(n)
    }
}

impl Read for VerilatorUart {
    fn read(&mut self, buf: &mut [u8]) -> std::io::Result<usize> {
        self.file.read(buf)
    }
}

impl Write for VerilatorUart {
    fn write(&mut self, buf: &[u8]) -> std::io::Result<usize> {
        self.file.write(buf)
    }

    fn flush(&mut self) -> std::io::Result<()> {
        self.file.flush()
    }
}
