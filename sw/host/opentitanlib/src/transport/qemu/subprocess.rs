// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
use std::env;
use std::ffi::OsString;
use std::fs::File;
use std::io::ErrorKind;
use std::path::PathBuf;
use std::process::{Child, Command, Stdio};
use std::time::Duration;

use anyhow::Context;
use tempfile::TempDir;

/// Qemu startup options.
pub struct Options {
    /// The QEMU executable.
    pub executable: PathBuf,

    /// QEMU machine name, e.g. "ot-earlgrey".
    pub machine: String,

    /// QEMU machine properties.
    pub machine_props: Vec<String>,

    /// Path to the ROM image used to boot the CPU.
    pub rom_image: Option<PathBuf>,

    /// Path to the flash image.
    pub flash_image: Option<PathBuf>,

    /// Path to an OTP image.
    pub otp_image: Option<PathBuf>,

    /// Any extra arguments to QEMU.
    pub extra_args: Vec<OsString>,

    /// Timeout for starting QEMU.
    pub timeout: Duration,
}

/// This struct is responsible for managing a QEMU subprocess launched here.
pub struct Subprocess {
    /// QEMU subprocess.
    child: Child,

    /// Directory where files and sockets for IO connections to QEMu are stored.
    ///
    /// Removed when dropped.
    connection_dir: TempDir,
}

impl Subprocess {
    const UART0_FILE: &str = "uart0";

    /// Starts a QEMU [`Subprocess`] based on [`Options`].
    pub fn from_options(options: Options) -> anyhow::Result<Self> {
        let mut command = Command::new(&options.executable);

        // Join the machine name with machine properties by commas.
        let machine = options
            .machine_props
            .iter()
            .fold(options.machine, |mut s, prop| {
                s.push(',');
                s.push_str(prop);
                s
            });
        command.args(["-machine", &machine]);

        // Add arguments for specified images:

        if let Some(rom_image) = options.rom_image {
            command.arg("-object");
            command.arg(format!(
                "ot-rom-img,id=rom,file={rom_image},digest=fake",
                rom_image = rom_image.display()
            ));
        }

        // NOTE: We load these drives as `readonly` because Bazel can
        // only provide readonly test inputs. To support tests which modify
        // flash or OTP, we will need to make writable copies of the images
        // ourselves.

        if let Some(flash_image) = options.flash_image {
            command.arg("-drive");
            command.arg(format!(
                "if=mtd,bus=1,file={},format=raw,readonly=on",
                flash_image.display()
            ));
        }

        if let Some(otp_image) = options.otp_image {
            command.arg("-drive");
            command.arg(format!(
                "if=pflash,file={},format=raw,readonly=on",
                otp_image.display()
            ));
        }

        // Create files for QEMU to connect IO to.
        let connection_dir = tempfile::tempdir().context("failed to create tempdir")?;

        let uart_path = connection_dir.path().join(Self::UART0_FILE);

        // Create the file so we can open it when we like without waiting for QEMU to create it.
        File::create(&uart_path).context("failed to create UART file")?;

        command.arg("-chardev");
        command.arg(format!("file,id=uart0,path={}", uart_path.display()));
        command.args(["-serial", "chardev:uart0"]);

        // Add explicitly requested arguments.
        command.args(options.extra_args.as_slice());

        log::info!("CWD: {:?}", env::current_dir());
        log::info!(
            "Spawning QEMU: {} {}",
            options.executable.display(),
            command
                .get_args()
                .map(|s| s.to_string_lossy())
                .collect::<Vec<_>>()
                .join(" ")
        );

        // Start QEMU.
        let child = command
            .stdin(Stdio::null())
            .stdout(Stdio::inherit())
            .stderr(Stdio::inherit())
            .spawn()?;

        Ok(Subprocess {
            child,
            connection_dir,
        })
    }

    pub fn uart_path(&self) -> PathBuf {
        self.connection_dir.path().join(Self::UART0_FILE)
    }

    /// Kill the QEMU subprocess.
    pub fn kill(&mut self) -> anyhow::Result<()> {
        match self.child.kill() {
            Err(error) if error.kind() != ErrorKind::InvalidInput => Err(error.into()),
            _ => Ok(()),
        }
    }
}
