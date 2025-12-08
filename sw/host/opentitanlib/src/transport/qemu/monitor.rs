// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use std::io::{BufRead, BufReader, Write};
use std::os::unix::net::UnixStream;
use std::path::{Path, PathBuf};

use anyhow::{Context, bail, ensure};
use serde::Deserialize;

/// Interface to QEMU's monitor.
///
/// The monitor is expected to be configured in `control` mode for the JSON QMP
/// protocol, not "human" mode.
pub struct Monitor {
    /// Unix Stream (socket) connected to QEMU's monitor.
    stream: BufReader<UnixStream>,

    /// Incrementing ID attached to each command and checked with each response.
    id_counter: usize,

    /// Whether to quit QEMU when dropped.
    quit_qemu: bool,
}

/// A value of a property on an object in the QEMU Object Model (QOM)
pub enum QomPropertyValue {
    String(String),
    Int(u64),
    Bool(bool),
}

impl Monitor {
    /// Connect to the QEMU monitor over a given socket.
    pub fn new<P: AsRef<Path>>(socket_path: P, quit_qemu: bool) -> anyhow::Result<Self> {
        let socket_path = socket_path
            .as_ref()
            .to_str()
            .context("monitor socket path not UTF8")?;
        let stream =
            UnixStream::connect(socket_path).context("failed to connect to QEMU Monitor socket")?;
        stream.set_read_timeout(None)?;

        let mut stream = BufReader::new(stream);

        // QMP sends us a greeting line on every connection:
        let mut greeting = String::new();
        stream
            .read_line(&mut greeting)
            .context("expected greeting line from QEMU monitor")?;

        // Check the greeting:
        let Greeting {
            qmp: Qmp { version, .. },
        } = serde_json::from_str(greeting.as_str()).context("failed to parse QEMU QMP greeting")?;
        log::info!(
            "connected to QEMU version {major}.{minor}.{micro}",
            major = version.qemu.major,
            minor = version.qemu.minor,
            micro = version.qemu.micro
        );

        let mut monitor = Monitor {
            stream,
            id_counter: 0,
            quit_qemu,
        };

        // Negotiate capabilities.
        // We don't need any, but the protocol requires us to do this.
        monitor.send_cmd("qmp_capabilities", None)?;

        Ok(monitor)
    }

    /// Send a continue command either starting or resuming the emulation.
    pub fn cont(&mut self) -> anyhow::Result<()> {
        self.send_cmd("cont", None)?;

        Ok(())
    }

    /// Stop the emulation (resumable, does not quit QEMU).
    pub fn stop(&mut self) -> anyhow::Result<()> {
        self.send_cmd("stop", None)?;

        Ok(())
    }

    /// Reset the system within the emulation.
    pub fn reset(&mut self) -> anyhow::Result<()> {
        self.send_cmd("system_reset", None)?;

        Ok(())
    }

    /// Gracefully shut down QEMU and terminate the process.
    pub fn quit(&mut self) -> anyhow::Result<()> {
        self.send_cmd("quit", None)?;

        Ok(())
    }

    /// List the IDs of the currently configured `chardev`s.
    pub fn query_chardevs(&mut self) -> anyhow::Result<Vec<Chardev>> {
        let response = self.send_cmd("query-chardev", None)?;
        let serde_json::Value::Array(response) = response else {
            bail!("expected array of chardevs");
        };

        let mut chardevs = Vec::new();
        for chardev in response {
            let chardev = serde_json::from_value(chardev).context("failed to parse chardev")?;
            chardevs.push(chardev);
        }

        Ok(chardevs)
    }

    // Send a break condition over a specified CharDev
    pub fn send_chardev_break(&mut self, id: &str) -> anyhow::Result<()> {
        self.send_cmd(
            "chardev-send-break",
            Some(format!(r#"{{"id": "{id}"}}"#).as_str()),
        )?;

        Ok(())
    }

    // Set a QOM Property of a QEMU device
    pub fn set_property(
        &mut self,
        object_path: Option<&str>,
        property: &str,
        value: &QomPropertyValue,
    ) -> anyhow::Result<()> {
        let path = object_path.unwrap_or("/machine");
        let value = match value {
            QomPropertyValue::String(s) => format!(r#""{s}""#),
            QomPropertyValue::Int(i) => format!("{i}"),
            QomPropertyValue::Bool(b) => format!("{b}"),
        };
        self.send_cmd(
            "qom-set",
            Some(
                format!(
                    r#"{{"path": "{path}",
                    "property": "{property}",
                    "value": {value}}}"#
                )
                .as_str(),
            ),
        )?;

        Ok(())
    }

    /// Send a command over the JSON QMP interface.
    ///
    /// The protocol goes:
    ///
    /// 1. Send a command with the form `{ "execute": <cmd>, "arguments": <obj>, "id": <val> }`.
    /// 2. Skip any asynchronous event responses that arrived before the command.
    /// 3. Check the response for success (with optional value) or error.
    ///
    /// We only support synchronous commands, i.e. we wait for a response before
    /// sending anything new.
    fn send_cmd(&mut self, cmd: &str, args: Option<&str>) -> anyhow::Result<serde_json::Value> {
        let id = self.id_counter;

        let command = match args {
            Some(arguments) => {
                format!(r#"{{ "execute": "{cmd}", "arguments": {arguments}, "id": {id} }}"#)
            }
            None => format!(r#"{{ "execute": "{cmd}", "id": {id} }}"#),
        };

        writeln!(self.stream.get_mut(), "{}", command.as_str())?;

        // Increment the ID for the next message.
        self.id_counter += 1;

        // Find the response for this message, skipping over asynchronous events that came in
        // before we sent our command.
        let response = loop {
            let mut line = String::new();
            self.stream.read_line(&mut line)?;

            let response: MonitorResponse = serde_json::from_str(&line)
                .with_context(|| format!("unexpected response: {line}"))?;

            // Skip asynchronous event responses.
            if let MonitorResponse::Event { .. } = response {
                continue;
            }

            break response;
        };

        // Check for success/failure, extracting the return value for successes.
        match response {
            MonitorResponse::Success {
                r#return,
                id: resp_id,
            } => {
                ensure!(id == resp_id, "response ID did not match request ID");
                Ok(r#return)
            }
            MonitorResponse::Error { id: resp_id, error } => {
                ensure!(id == resp_id, "response ID did not match request ID");
                bail!("monitor returned error: {error:#?}");
            }
            MonitorResponse::Event { .. } => unreachable!("should have been skipped"),
        }
    }
}

impl Drop for Monitor {
    fn drop(&mut self) {
        // Quit QEMU when dropped if requested.
        if self.quit_qemu {
            self.quit().ok();
        }
    }
}

/// Possible responses from the server.
#[derive(Deserialize)]
#[serde(untagged)]
enum MonitorResponse {
    /// Command with `id` was successful and has optional return value.
    Success {
        id: usize,
        r#return: serde_json::Value,
    },
    /// Command with `id` gave an error with some extra details.
    Error { id: usize, error: serde_json::Value },
    /// Asynchronous event arrived outside of our commands.
    Event {
        #[serde(rename = "event")]
        _event: String,
        #[serde(rename = "timestamp")]
        _timestamp: serde_json::Value,
        #[serde(rename = "data", default)]
        _data: serde_json::Value,
    },
}

/// Greeting message when connecting to QEMU.
#[derive(Deserialize)]
struct Greeting {
    #[serde(alias = "QMP")]
    qmp: Qmp,
}

/// QMP protocol information.
#[derive(Deserialize)]
struct Qmp {
    /// Current version.
    version: Version,
    /// Optional capabilities of the monitor.
    #[serde(rename = "capabilities")]
    _capabilities: Vec<String>,
}

/// QMP version information.
#[derive(Deserialize)]
struct Version {
    qemu: QemuVersion,

    #[serde(rename = "package")]
    _package: String,
}

/// QEMU version information.
#[derive(Deserialize)]
struct QemuVersion {
    major: usize,
    minor: usize,
    micro: usize,
}

/// Response from QEMU's `query-chardev` describing a character device.
#[derive(Debug, Deserialize)]
struct ChardevJson {
    label: String,
    filename: String,

    #[serde(rename = "frontend_open")]
    _frontend_open: Option<bool>,
}

/// Nicer version of the chardev info that QEMU sends us.
#[derive(Clone, Debug, Deserialize)]
#[serde(try_from = "ChardevJson")]
pub struct Chardev {
    pub id: String,
    pub kind: ChardevKind,
}

/// Possible kinds of supported chardevs.
#[derive(Clone, Debug)]
pub enum ChardevKind {
    Pty { path: PathBuf },
    Socket { path: PathBuf },
    Other,
}

impl TryFrom<ChardevJson> for Chardev {
    type Error = anyhow::Error;

    fn try_from(json: ChardevJson) -> anyhow::Result<Chardev> {
        let kind = if let Some(path) = json.filename.strip_prefix("pty:") {
            let path = PathBuf::from(path);
            ChardevKind::Pty { path }
        } else if let Some(sock) = json.filename.strip_prefix("disconnected:unix:") {
            let path = sock
                .split(',')
                .next()
                .with_context(|| format!("bad socket path format: {sock}"))?;
            let path = PathBuf::from(path);
            ChardevKind::Socket { path }
        } else {
            ChardevKind::Other
        };

        let chardev = Chardev {
            id: json.label,
            kind,
        };

        Ok(chardev)
    }
}
