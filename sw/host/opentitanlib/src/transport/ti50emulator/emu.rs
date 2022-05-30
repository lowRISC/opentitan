// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use std::cell::RefCell;
use std::collections::{HashMap, HashSet};
use std::ffi::OsString;
use std::fs;
use std::io::{ErrorKind, Read};
use std::os::unix::net::UnixListener;
use std::path::{Path, PathBuf};
use std::process::{Child, Command};
use std::rc::Rc;
use std::time::Duration;

use anyhow::{bail, Context, Result};
use log;
use nix::sys::signal::{self, Signal};
use nix::unistd::Pid;

use crate::io::emu::{EmuError, EmuState, EmuValue, Emulator};
use crate::transport::ti50emulator::Inner;
use crate::transport::ti50emulator::Ti50Emulator;

const TIMEOUT: Duration = Duration::from_millis(1000);
const MAX_RETRY: usize = 5;
const PATTERN: &[u8; 5] = b"READY";
pub const EMULATOR_INVALID_ID: u64 = 0;

pub struct EmulatorProcess {
    /// Current working directory for Emulator sub-process.
    runtime_directory: PathBuf,
    /// Directory with contain TockOS Applications and Kernel.
    executable_directory: PathBuf,
    /// Default name of TockOS kernel file.
    executable: String,
    /// Map of currently used argument by kernel.
    current_args: HashMap<String, EmuValue>,
    /// Current state of Emulator.
    state: EmuState,
    /// Handle to Emulator sub-proccess.
    proc: Option<Child>,
    /// Counter of 'power' cycle
    power_cycle_count: u32,
}

impl EmulatorProcess {
    /// Create new instance of [`EmulatorProcess`] based on provided parameters.
    pub fn init(
        instance_directory: &Path,
        executable_directory: &Path,
        executable: &str,
    ) -> Result<Self> {
        let runtime_directory = instance_directory.join("runtime");
        fs::create_dir(&runtime_directory).context("Failed to create runtime directory")?;
        Ok(Self {
            executable_directory: executable_directory.to_owned(),
            executable: executable.to_owned(),
            runtime_directory: runtime_directory.clone(),
            current_args: HashMap::from([(
                String::from("exec"),
                EmuValue::String(String::from(executable)),
            )]),
            state: EmuState::Off,
            proc: None,
            power_cycle_count: 1,
        })
    }

    pub fn get_state(&self) -> EmuState {
        self.state
    }

    pub fn get_runtime_dir(&self) -> &Path {
        &self.runtime_directory
    }

    pub fn get_id(&self) -> u64 {
        if let Some(proc) = &self.proc {
            return ((self.power_cycle_count as u64) << 32) + (proc.id() as u64);
        }
        return EMULATOR_INVALID_ID;
    }

    /// Updates `state` based on sub-process exit status and current value of `state`.
    pub fn update_status(&mut self) -> Result<()> {
        if let Some(proc) = &mut self.proc {
            match proc.try_wait() {
                Ok(Some(status)) => {
                    if status.success() {
                        log::info!("Ti50Emulator exit with status {}", status);
                        self.state = EmuState::Off;
                    } else {
                        if self.state != EmuState::Error {
                            log::info!("Ti50Emulator sub-process exit with error: {}", status);
                            self.state = EmuState::Error;
                        }
                    }
                    self.power_cycle_count += 1;
                    self.proc = None;
                }
                Ok(None) => {
                    self.state = EmuState::On;
                }
                Err(err) => {
                    bail!(EmuError::RuntimeError(format!(
                        "Can't aquire status from sub-process pid:{} error:{}",
                        proc.id(),
                        err
                    )));
                }
            }
        } else {
            if self.state == EmuState::On {
                self.state = EmuState::Error;
                bail!(EmuError::RuntimeError(
                    "Non sub-process found but state indicate that Emulator is ON".to_string()
                ));
            }
        }
        Ok(())
    }

    /// Run Emulator executable as sub-process and wait until Emulator is ready to work.
    fn spawn_process(&mut self) -> Result<()> {
        let socket_path = self.runtime_directory.join("control_soc");
        let control_socket = UnixListener::bind(&socket_path)?;
        control_socket
            .set_nonblocking(true)
            .context("Set non-blocking to socket fail")?;

        let mut args_list = Vec::new();

        args_list.push(OsString::from("--path"));
        args_list.push(self.runtime_directory.clone().into_os_string());

        args_list.push(OsString::from("--control_socket"));
        args_list.push(socket_path.into_os_string());

        match self.current_args.get("apps") {
            Some(EmuValue::StringList(apps)) => {
                args_list.push(OsString::from("--apps"));
                args_list.extend(
                    apps.iter()
                        .map(|a| self.executable_directory.join(a).into()),
                );
            }
            None => {
                bail!(EmuError::StartFailureCause(
                    "Ti50 sub-process missing application list".to_string()
                ))
            }
            _ => {
                bail!(EmuError::StartFailureCause(
                    "Ti50 sub-process expect apps to be list of string".to_string()
                ));
            }
        }

        let exec = match self.current_args.get("exec") {
            Some(EmuValue::String(exec_name)) => self.executable_directory.join(exec_name),
            None => {
                bail!(EmuError::StartFailureCause(
                    "Ti50 sub-process invalid executable".to_string()
                ))
            }
            _ => {
                bail!(EmuError::StartFailureCause(
                    "Ti50 sub-process except exec name to be string".to_string()
                ))
            }
        };

        log::info!("Spawning Ti50Emulator sub-process");
        log::info!("Command: {} {:?}", exec.display(), args_list);
        let handle = Command::new(&exec)
            .args(args_list)
            .spawn()
            .context("Could not spawn sub-process")?;
        self.proc = Some(handle);
        let mut buffer = [0u8, 8];
        let mut retry = 0;
        while retry < MAX_RETRY {
            match control_socket.accept() {
                Ok((mut socket, _address)) => {
                    let len = socket
                        .read(&mut buffer)
                        .context("Control socket read error")?;
                    if len >= PATTERN.len() && PATTERN[..] == buffer[0..PATTERN.len()] {
                        log::info!("Ti50Emulator ready");
                        return Ok(());
                    }
                }
                Err(err) if err.kind() == ErrorKind::WouldBlock => {
                    log::debug!("Wait for sub-process...");
                    std::thread::sleep(TIMEOUT);
                }
                Err(err) => {
                    self.state = EmuState::Error;
                    bail!(EmuError::StartFailureCause(format!(
                        "Can't connect to other end of sub-process control socket error:{}",
                        err
                    )));
                }
            }
            retry += 1;
        }
        Err(EmuError::StartFailureCause(format!(
            "Ti50 sub-process spawn failure to many tries MAX_RETRY: {}",
            MAX_RETRY
        ))
        .into())
    }

    /// The function tries to safely terminate the Emulator sub-process.
    /// If the sub-process does not finish its execution after time
    /// described in `TIMEOUT` * `MAX_RETRY`, use SIGKILL to force sub-process termination.
    /// If all method fail, it returns an EmuError.
    fn stop_process(&mut self) -> Result<()> {
        self.power_cycle_count += 1;
        if let Some(handle) = &self.proc {
            let pid = handle.id() as i32;
            signal::kill(Pid::from_raw(pid), Signal::SIGTERM)
                .context("Stop sub-process using SIGTERM")?;
            for _retry in 0..MAX_RETRY {
                std::thread::sleep(TIMEOUT);
                match signal::kill(Pid::from_raw(pid), None) {
                    Ok(()) => {}
                    Err(nix::Error::Sys(nix::errno::Errno::ESRCH)) => {
                        self.state = EmuState::Off;
                        self.proc = None;
                        return Ok(());
                    }
                    Err(e) => {
                        self.state = EmuState::Error;
                        bail!(EmuError::StopFailureCause(format!(
                            "Unexpected error querying process presence: {}",
                            e
                        )));
                    }
                }
            }
            signal::kill(Pid::from_raw(pid), Signal::SIGKILL)
                .context("Stop sub-process using SIGKILL")?;
            std::thread::sleep(TIMEOUT);
            match signal::kill(Pid::from_raw(pid), None) {
                Err(nix::Error::Sys(nix::errno::Errno::ESRCH)) => {
                    self.proc = None;
                    self.state = EmuState::Off;
                    return Ok(());
                }
                _ => {
                    self.proc = None;
                    self.state = EmuState::Error;
                    bail!(EmuError::StopFailureCause(format!(
                        "Unable to stop process pid:{}",
                        pid
                    )));
                }
            }
        }
        Ok(())
    }

    /// Method reset all internal states of Emulator to its default values.
    fn reset_state(&mut self) -> Result<()> {
        fs::remove_dir_all(&self.runtime_directory)?;
        fs::create_dir(&self.runtime_directory)?;
        self.current_args.clear();
        self.current_args.insert(
            String::from("exec"),
            EmuValue::String(self.executable.clone()),
        );
        Ok(())
    }

    /// Update content of resource with data from `source`, overwrite file if it already exist.
    fn update_resource(&self, key: &str, source: &Path) -> Result<()> {
        let name = source.file_name().ok_or(EmuError::InvalidArgumentValue(
            String::from(key),
            source.display().to_string(),
        ))?;
        let destination = self.runtime_directory.join(name);
        log::debug!(
            "Update resource:{:?} with data from path: {:?}",
            key,
            source,
        );
        fs::copy(&source, &destination).with_context(|| {
            format!(
                "Failed to copy resource file: {} to runtime directory: {}",
                &source.display(),
                &destination.display()
            )
        })?;
        Ok(())
    }

    /// Method update state files and parameters passed to Emulator sub-process.
    /// If `factory_reset` is set to true old resource files stored in runtime_directory will be removed and
    /// current_args will be set to its default value.
    /// Values from parameter `args` is used to update value of current argument set passed to
    /// sub-process. If `args` contains paths to files they will be copied to the runtime directory.
    fn update_args(&mut self, factory_reset: bool, args: &HashMap<String, EmuValue>) -> Result<()> {
        let allowed = HashSet::from(["exec", "flash", "apps", "version_state", "pmu_state"]);
        let mandatory = ["exec", "apps"];
        for &name in mandatory.iter() {
            if !self.current_args.contains_key(name) && !args.contains_key(name) {
                bail!(EmuError::StartFailureCause(format!(
                    "Missing argument {}",
                    name
                )))
            }
        }
        if factory_reset {
            self.reset_state()?;
        }
        for (key, item) in args.iter() {
            if allowed.contains(key.as_str()) {
                match item {
                    EmuValue::FilePath(path) => {
                        self.update_resource(&key, path)?;
                    }
                    EmuValue::FilePathList(path_list) => {
                        for path in path_list.iter() {
                            self.update_resource(&key, path)?;
                        }
                    }
                    _ => {}
                }
                self.current_args.insert(key.clone(), item.clone());
                continue;
            }
            bail!(EmuError::InvalidArgumetName(key.clone()));
        }
        Ok(())
    }
}

/// Structure representing `Emulator` sub-process based on TockOS host-emulation architecture.
pub struct Ti50SubProcess {
    inner: Rc<RefCell<Inner>>,
}

impl Ti50SubProcess {
    /// Create a new `Ti50SubProcess` instance.
    pub fn open(ti50: &Ti50Emulator) -> Result<Self> {
        Ok(Self {
            inner: ti50.inner.clone(),
        })
    }
}

impl Emulator for Ti50SubProcess {
    /// Simple function with return `EmuState` representing current state of Emulator instance.
    fn get_state(&self) -> Result<EmuState> {
        let process = &mut self.inner.borrow_mut().process;
        process.update_status()?;
        Ok(process.state)
    }

    /// Start emulator sub-process with provided arguments.
    fn start(&self, factory_reset: bool, args: &HashMap<String, EmuValue>) -> Result<()> {
        let process = &mut self.inner.borrow_mut().process;
        process.update_status()?;
        match process.state {
            EmuState::On => {
                bail!(EmuError::StartFailureCause(String::from(
                    "DUT is already running",
                )));
            }
            EmuState::Busy => {
                bail!(EmuError::StartFailureCause(String::from(
                    "DUT is in transient state BUSY",
                )));
            }
            EmuState::Error => {
                log::debug!("DUT trying to recover after error");
            }
            _ => {}
        };
        process.state = EmuState::Busy;
        process.update_args(factory_reset, args)?;
        process.spawn_process()?;
        process.state = EmuState::On;
        Ok(())
    }

    /// Stop emulator sub-process.
    fn stop(&self) -> Result<()> {
        let process = &mut self.inner.borrow_mut().process;
        process.update_status()?;
        match process.state {
            EmuState::Off => {
                bail!(EmuError::StopFailureCause(String::from(
                    "DUT is alredy Off"
                ),));
            }
            EmuState::Busy => {
                bail!(EmuError::StopFailureCause(String::from(
                    "DUT is in transient state BUSY"
                ),));
            }
            EmuState::Error => {
                log::info!("DUT stop after error");
            }
            _ => {}
        }
        process.stop_process()?;
        Ok(())
    }
}
