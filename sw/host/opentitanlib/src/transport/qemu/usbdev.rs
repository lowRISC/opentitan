// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::{Context, anyhow};
use num_enum::{IntoPrimitive, TryFromPrimitive};
use serialport::TTYPort;
use std::cell::{Cell, RefCell};
use std::io::{Read, Write};
use std::sync::mpsc;
use std::thread;
use std::time::Duration;
use thiserror::Error;
use zerocopy::{FromBytes, Immutable, IntoBytes, KnownLayout, Unaligned, byteorder::little_endian};

use crate::io::gpio::{GpioPin, PinMode, PullMode};
use crate::io::usb::{UsbContext as OtUsbContext, UsbDevice, desc};

/// Pin-like interface for controlling USB VBUS.
pub struct QemuVbusSense {
    pub usbdev: RefCell<TTYPort>,
    pub asserted: Cell<bool>,
}

impl QemuVbusSense {
    pub fn new(usbdev: TTYPort) -> QemuVbusSense {
        QemuVbusSense {
            usbdev: RefCell::new(usbdev),
            asserted: Cell::new(false),
        }
    }
}

impl GpioPin for QemuVbusSense {
    fn read(&self) -> anyhow::Result<bool> {
        Ok(self.asserted.get())
    }

    fn write(&self, value: bool) -> anyhow::Result<()> {
        if value == self.asserted.get() {
            return Ok(());
        }

        let cmd = if value { "vbus_on" } else { "vbus_off" };
        writeln!(*self.usbdev.borrow_mut(), "{}", cmd)?;

        self.asserted.set(value);

        Ok(())
    }

    fn set_mode(&self, _mode: PinMode) -> anyhow::Result<()> {
        Ok(())
    }

    fn set_pull_mode(&self, _mode: PullMode) -> anyhow::Result<()> {
        Ok(())
    }

    fn set(
        &self,
        _mode: Option<PinMode>,
        value: Option<bool>,
        _pull: Option<PullMode>,
        _analog_value: Option<f32>,
    ) -> anyhow::Result<()> {
        if let Some(value) = value {
            return self.write(value);
        }

        Ok(())
    }
}

/// Events sent by otlib to the virtual host thread.
enum HostChannelEvent {
    /// A message was sent by QEMU to the host.
    QemuMessage { cmd: u32, id: u32, data: Vec<u8> },
}

/// Minimal virtual USB host to drive the QEMU usbdev.
pub struct QemuUsbHost {
    /// Sender to notify the virtual host thread of various events
    /// from the otlib side.
    _host_channel: mpsc::Sender<HostChannelEvent>,
}

impl QemuUsbHost {
    pub fn new(usbdev: TTYPort) -> QemuUsbHost {
        let (send, recv) = mpsc::channel();
        let send_thread = send.clone();
        thread::spawn(move || {
            let mut host_thread = QemuHostThread::new(usbdev, send_thread, recv);
            if let Err(UsbError::Other(err)) = host_thread.run() {
                log::error!("QEMU USB host failed with error: {err:?}");
            };
        });

        QemuUsbHost {
            _host_channel: send,
        }
    }
}

impl OtUsbContext for QemuUsbHost {
    fn device_by_id_with_timeout(
        &self,
        _usb_vid: u16,
        _usb_pid: u16,
        _usb_serial: Option<&str>,
        _timeout: Duration,
    ) -> anyhow::Result<Box<dyn UsbDevice>> {
        unimplemented!();
    }

    fn device_by_interface_with_timeout(
        &self,
        _class: u8,
        _subclass: u8,
        _protocol: u8,
        _usb_serial: Option<&str>,
        _timeout: Duration,
    ) -> anyhow::Result<Box<dyn UsbDevice>> {
        unimplemented!();
    }
}

/// USBDEV Command, see QEMU documentation.
#[repr(u32)]
#[allow(dead_code)]
#[derive(Debug, Eq, PartialEq, TryFromPrimitive, IntoPrimitive, Clone, Copy)]
enum QemuUsbdevCmd {
    Invalid,
    Hello,
    VbusOn,
    VbusOff,
    Connect,
    Disconnect,
    Reset,
    Resume,
    Suspend,
    Setup,
    Transfer,
    Complete,
}

/// USBDEV packet header, see QEMU documentation.
#[derive(Clone, FromBytes, IntoBytes, KnownLayout, Immutable, Unaligned)]
#[repr(C)]
pub struct QemuUsbdevPacketHeader {
    command: little_endian::U32,
    size: little_endian::U32,
    id: little_endian::U32,
}

/// USBDEV hello payload, see QEMU documentation.
#[derive(Clone, IntoBytes, FromBytes, KnownLayout, Immutable, Unaligned)]
#[repr(C)]
pub struct QemuUsbdevHelloPayload {
    magic: [u8; 4],
    major_version: little_endian::U16,
    minor_version: little_endian::U16,
}

/// USBDEV setup payload, see QEMU documentation.
#[derive(Clone, IntoBytes, KnownLayout, Immutable, Unaligned)]
#[repr(C)]
pub struct QemuUsbdevSetupPayload {
    address: u8,
    endpoint: u8,
    reserved: [u8; 2],
    setup: [u8; 8],
}

/// USBDEV transfer flags, see QEMU documentation.
#[repr(u8)]
#[allow(dead_code)]
#[derive(Debug, Eq, PartialEq, IntoPrimitive, Clone, Copy)]
enum QemuUsbdevTransferFlags {
    Zlp = 1 << 0,
}

/// USBDEV transfer payload, see QEMU documentation.
#[derive(Clone, IntoBytes, KnownLayout, Immutable, Unaligned)]
#[repr(C)]
pub struct QemuUsbdevTransferPayload {
    address: u8,
    endpoint: u8,
    max_packet_size: little_endian::U16,
    flags: u8,
    reserved: [u8; 3],
    transfer_size: little_endian::U32,
}

/// USBDEV transfer status, see QEMU documentation.
#[repr(u8)]
#[allow(dead_code)]
#[derive(Debug, Eq, PartialEq, TryFromPrimitive, Clone, Copy)]
enum QemuUsbdevTransferStatus {
    Success,
    Stalled,
    Cancelled,
    Error,
}

/// USBDEV complete payload, see QEMU documentation.
#[derive(Clone, FromBytes, Immutable, Unaligned)]
#[repr(C)]
pub struct QemuUsbdevCompletePayload {
    status: u8,
    reserved: [u8; 3],
    xfer_size: little_endian::U32,
}

/// Represents a packet ID.
#[derive(Debug, Clone, Copy, Eq, PartialEq)]
struct PacketId(u32);

/// This structure records an event received from QEMU on the chardev.
/// It only parses the packet header and passes the rest of the payload
/// as-is.
#[derive(Debug)]
struct QemuUsbdevEvent {
    cmd: QemuUsbdevCmd,
    id: PacketId,
    data: Vec<u8>,
}

/// This structure records a complete event received from QEMU on the chardev.
/// The complete payload is parsed and the received data is stored as-is.
#[derive(Debug)]
struct QemuUsbdevCompleteEvent {
    id: PacketId,
    status: QemuUsbdevTransferStatus,
    // Temporary until we have a more complete stack that uses this field.
    #[allow(dead_code)]
    xfer_size: u32,
    data: Vec<u8>,
}

/// Standard USB Setup packet.
#[derive(Clone, IntoBytes, KnownLayout, Immutable, Unaligned)]
#[repr(C)]
struct UsbSetupPacket {
    req_type: u8,
    request: u8,
    value: little_endian::U16,
    index: little_endian::U16,
    length: little_endian::U16,
}

#[derive(Error, Debug)]
enum UsbError {
    /// Shutdown was requested.
    #[error("USB host was told to shutdown")]
    Shutdown,
    /// Device disconnected.
    #[error("USB device was disconnected")]
    Disconnected,
    /// Transfer failed.
    #[error("USB transfer failed with error {0:?}, context is {1:?}")]
    TransferFailed(QemuUsbdevTransferStatus, anyhow::Error),
    /// Other error not worth tracking precisely.
    #[error("{0:?}")]
    Other(#[from] anyhow::Error),
}

/// Error type used when waiting for a specific QEMU event
/// that could get interrupted in some way.
type UsbResult<T> = Result<T, UsbError>;

trait UsbContext<T, E> {
    fn maybe_context<C>(self, context: C) -> Result<T, E>
    where
        C: std::fmt::Display + Send + Sync + 'static;
}

impl<T> UsbContext<T, UsbError> for UsbResult<T> {
    fn maybe_context<C>(self, ctx: C) -> UsbResult<T>
    where
        C: std::fmt::Display + Send + Sync + 'static,
    {
        let Err(err) = self else { return self };
        Err(match err {
            UsbError::TransferFailed(status, err) => {
                UsbError::TransferFailed(status, err.context(ctx))
            }
            UsbError::Other(err) => UsbError::Other(err.context(ctx)),
            err => err,
        })
    }
}

/// This structure represents an enumerated and configured device.
#[derive(Clone, Debug)]
// Temporary until we have a more complete stack that uses this field.
#[allow(dead_code)]
struct DeviceInfo {
    dev_desc: Vec<u8>,
    address: u8,
    configurations: Vec<Vec<u8>>,
}

struct ControlIn {
    addr: u8,
    ep: u8,
    req_type: u8,
    req: u8,
    value: u16,
    index: u16,
    length: usize,
    max_pkt_size: u16,
}

struct ControlOut<'a> {
    addr: u8,
    ep: u8,
    req_type: u8,
    req: u8,
    value: u16,
    index: u16,
    max_pkt_size: u16,
    data: &'a [u8],
}

/// This structure holds the state of the USB host thread.
struct QemuHostThread {
    /// Communication channel to QEMU USBDEV.
    usbdev: TTYPort,
    /// Channel to receive/send events from otlib and reader.
    channel_recv: mpsc::Receiver<HostChannelEvent>,
    channel_send: mpsc::Sender<HostChannelEvent>,
    /// Next ID.
    next_id: u32,
}

impl QemuHostThread {
    const USBDEV_HELLO_MAGIC: [u8; 4] = *b"UDCX";
    const USBDEV_HELLO_MAJOR: u16 = 1;
    const USBDEV_HELLO_MINOR: u16 = 0;

    /// Standard USB mask for EP IN in Setup packets.
    const USBDEV_TRANSFER_EP_IN: u8 = 1 << 7;

    // Every device must be able to handle 8 bytes packets.
    const USB_FS_SAFE_PACKET_SIZE: u16 = 8;

    // Some standard request types.
    const USB_REQ_TYPE_OUT: u8 = 0;
    const USB_REQ_TYPE_IN: u8 = 0x80;
    const USB_REQ_TYPE_STANDARD: u8 = 0;
    const USB_REQ_TYPE_DEVICE: u8 = 0;

    // Some standard USB requests.
    const USB_SET_ADDRESS: u8 = 5;
    const USB_GET_DESCRIPTOR: u8 = 6;
    const USB_SET_CONFIGURATION: u8 = 9;

    // Some standard descriptor types.
    const USB_DEVICE_DESCRIPTOR: u8 = 1;
    const USB_CONFIG_DESCRIPTOR: u8 = 2;

    // Location of the bMaxPacketSize field in the device descriptor.
    const USB_DEV_DESC_MAX_PACKET_SIZE_OFFSET: usize = 7;

    // How much time to wait after a SET_ADDRESS before moving on
    // to the rest of the enumeration sequence.
    // The specification requires that the device be ready after 2ms
    // but there is no guarantee that QEMU is running at a similiar
    // speed as the host so this delay is quite conservative.
    const SET_ADDRESS_WAIT_DELAY_MS: u64 = 10;

    fn new(
        usbdev: TTYPort,
        channel_send: mpsc::Sender<HostChannelEvent>,
        channel_recv: mpsc::Receiver<HostChannelEvent>,
    ) -> Self {
        QemuHostThread {
            usbdev,
            channel_recv,
            channel_send,
            next_id: 0,
        }
    }

    /// Send a message to the QEMU USBDEV driver. On success, return the ID
    /// of the packet.
    fn send_packet(&mut self, cmd: QemuUsbdevCmd, data: &[&[u8]]) -> UsbResult<PacketId> {
        let tot_len: usize = data.as_ref().iter().map(|data| data.len()).sum();
        let hdr = QemuUsbdevPacketHeader {
            command: u32::from(cmd).into(),
            size: (tot_len as u32).into(),
            id: self.next_id.into(),
        };

        let pkt_id = self.next_id;
        self.next_id += 1;

        self.usbdev
            .write_all(hdr.as_bytes())
            .context("Failed to write packet header to usbdev tty")?;
        for data in data {
            self.usbdev
                .write_all(data)
                .context("Failed to write packet data to usbdev tty")?;
        }
        self.usbdev.flush().context("Failed to flush usbdev tty")?;
        Ok(PacketId(pkt_id))
    }

    /// Send a Hello command and return the ID.
    fn send_hello(&mut self) -> UsbResult<PacketId> {
        let hello = QemuUsbdevHelloPayload {
            magic: Self::USBDEV_HELLO_MAGIC,
            major_version: Self::USBDEV_HELLO_MAJOR.into(),
            minor_version: Self::USBDEV_HELLO_MINOR.into(),
        };

        self.send_packet(QemuUsbdevCmd::Hello, &[hello.as_bytes()])
    }

    /// Send a Setup command and return the ID.
    fn send_setup(&mut self, addr: u8, ep: u8, setup: &[u8; 8]) -> UsbResult<PacketId> {
        let setup_cmd = QemuUsbdevSetupPayload {
            address: addr,
            endpoint: ep,
            reserved: [0u8; 2],
            setup: *setup,
        };
        self.send_packet(QemuUsbdevCmd::Setup, &[setup_cmd.as_bytes()])
    }

    /// Send a Transfer command and return the ID.
    fn send_transfer_internal(
        &mut self,
        addr: u8,
        ep: u8,
        flags: u8,
        max_pkt_size: u16,
        transfer_size: u32,
        data: &[u8],
    ) -> UsbResult<PacketId> {
        let xfer_cmd = QemuUsbdevTransferPayload {
            address: addr,
            endpoint: ep,
            max_packet_size: max_pkt_size.into(),
            flags,
            reserved: [0u8; 3],
            transfer_size: transfer_size.into(),
        };

        self.send_packet(QemuUsbdevCmd::Transfer, &[xfer_cmd.as_bytes(), data])
    }

    /// Helper function to send a Transfer IN command and return the ID.
    fn send_transfer_in(
        &mut self,
        addr: u8,
        ep: u8,
        max_pkt_size: u16,
        transfer_size: usize,
    ) -> UsbResult<PacketId> {
        self.send_transfer_internal(
            addr,
            ep | Self::USBDEV_TRANSFER_EP_IN,
            /* flags */ 0,
            max_pkt_size,
            transfer_size as u32,
            &[],
        )
    }

    /// Helper function to send a Transfer OUT command and return the ID.
    fn send_transfer_out(
        &mut self,
        addr: u8,
        ep: u8,
        zlp: bool,
        max_pkt_size: u16,
        data: &[u8],
    ) -> UsbResult<PacketId> {
        let flags: u8 = if zlp {
            QemuUsbdevTransferFlags::Zlp.into()
        } else {
            0
        };
        self.send_transfer_internal(addr, ep, flags, max_pkt_size, data.len() as u32, data)
    }

    /// Send a Setup command followed by a Transfer IN command of the requested length.
    /// Return the ID of the expected Complete event corresponding to the data IN.
    fn send_control_in(&mut self, control: &ControlIn) -> UsbResult<PacketId> {
        let setup = UsbSetupPacket {
            req_type: control.req_type,
            request: control.req,
            value: control.value.into(),
            index: control.index.into(),
            length: u16::try_from(control.length)
                .context("control IN length does not fit in 16 bits")?
                .into(),
        };
        let _ = self
            .send_setup(
                control.addr,
                control.ep,
                setup.as_bytes().try_into().unwrap(),
            )
            .maybe_context("Failed to send SETUP for control in")?;
        self.send_transfer_in(
            control.addr,
            control.ep,
            control.max_pkt_size,
            control.length,
        )
    }

    /// Send a Setup command followed by a Transfer OUT command of the required length.
    /// Return the ID of the expected Complete event corresponding to the data OUT, or
    /// None if there is no data stage.
    fn send_control_out<'a>(&mut self, control: &ControlOut<'a>) -> UsbResult<Option<PacketId>> {
        let setup = UsbSetupPacket {
            req_type: control.req_type,
            request: control.req,
            value: control.value.into(),
            index: control.index.into(),
            length: u16::try_from(control.data.len())
                .context("control OUT length does not fit in 16 bits")?
                .into(),
        };
        let _ = self
            .send_setup(
                control.addr,
                control.ep,
                setup.as_bytes().try_into().unwrap(),
            )
            .maybe_context("Failed to send SETUP for control in")?;
        if control.data.is_empty() {
            return Ok(None);
        }
        Ok(Some(self.send_transfer_out(
            control.addr,
            control.ep,
            /* zlp */ false,
            control.max_pkt_size,
            control.data,
        )?))
    }

    /// Wait for a QEMU command and return its payload. Return an error if something goes
    /// wrong.
    fn wait_qemu_event(&mut self) -> UsbResult<QemuUsbdevEvent> {
        let Ok(event) = self.channel_recv.recv() else {
            return Err(UsbError::Shutdown);
        };
        Ok(match event {
            HostChannelEvent::QemuMessage { cmd, id, data } => {
                let cmd = QemuUsbdevCmd::try_from(cmd)
                    .with_context(|| format!("Unknown command {cmd} from USBDEV"))?;
                QemuUsbdevEvent {
                    cmd,
                    id: PacketId(id),
                    data,
                }
            }
        })
    }

    /// Wait for a HELLO packet and return the payload. Return an error if something goes
    /// wrong or an unexpected packet is received.
    fn wait_hello(&mut self, expected_id: PacketId) -> UsbResult<QemuUsbdevHelloPayload> {
        let QemuUsbdevEvent { cmd, id, data } = self.wait_qemu_event()?;
        if cmd != QemuUsbdevCmd::Hello {
            Err(anyhow!("Expected a HELLO event, got {cmd:?}"))?;
        }
        if id != expected_id {
            Err(anyhow!("Expected HELLO with {expected_id:?}, got {id:?}"))?;
        }
        let (payload, data) = QemuUsbdevHelloPayload::read_from_prefix(&data)
            .map_err(|err| anyhow!("{err:?}"))
            .context("Could not parse HELLO payload")?;
        if !data.is_empty() {
            Err(anyhow!(
                "HELLO payload is larger than expected by {} bytes",
                data.len()
            ))?;
        }
        if payload.magic != Self::USBDEV_HELLO_MAGIC {
            Err(anyhow!(
                "HELLO payload has the wrong magic bytes: {:?}",
                payload.magic
            ))?;
        }
        Ok(payload)
    }

    /// Wait for a CONNECT packet and return the ID. Return an error if something goes
    /// wrong or an unexpected packet is received.
    fn wait_connect(&mut self) -> UsbResult<PacketId> {
        let QemuUsbdevEvent { cmd, id, data } = self.wait_qemu_event()?;
        // If the device was previously disconnected, the only valid event that the device
        // can send is a CONNECT event.
        if cmd != QemuUsbdevCmd::Connect {
            Err(anyhow!("Expected a CONNECT event, got {cmd:?}"))?;
        }
        if !data.is_empty() {
            Err(anyhow!("CONNECT payload is non-empty"))?;
        }
        Ok(id)
    }

    /// Wait for a COMPLETE packet and return the data. Return an error if something goes
    /// wrong.
    fn wait_complete(&mut self) -> UsbResult<QemuUsbdevCompleteEvent> {
        let QemuUsbdevEvent { cmd, id, data } = self.wait_qemu_event()?;

        match cmd {
            QemuUsbdevCmd::Disconnect => Err(UsbError::Disconnected),
            QemuUsbdevCmd::Complete => {
                let (payload, data) = QemuUsbdevCompletePayload::read_from_prefix(&data)
                    .map_err(|err| anyhow!("{err:?}"))
                    .context("Could not parse Complete payload")?;
                // FIXME here it is somewhat inefficient because we are taking a slice of the
                // data and turning into back into vector...
                Ok(QemuUsbdevCompleteEvent {
                    id,
                    status: QemuUsbdevTransferStatus::try_from(payload.status).with_context(
                        || format!("Unknown transfer status {} from USBDEV", payload.status),
                    )?,
                    xfer_size: payload.xfer_size.into(),
                    data: data.to_vec(),
                })
            }
            _ => Err(anyhow!("unexpected event {cmd:?}").into()),
        }
    }

    /// Perform a full control IN transaction:
    /// - send a Setup
    /// - send a Transfer IN
    /// - wait for data IN
    /// - send a Transfer OUT (status stage)
    /// - wait for status
    fn send_and_wait_control_in(&mut self, control: &ControlIn) -> UsbResult<Vec<u8>> {
        let expected_id = self
            .send_control_in(control)
            .context("Failed to send control IN transfer")?;
        let QemuUsbdevCompleteEvent {
            id, status, data, ..
        } = self
            .wait_complete()
            .context("Failed to receive control IN data")?;
        if id != expected_id {
            Err(anyhow!(
                "Expected control IN data complete command ID with {expected_id:?}, got {id:?}"
            ))?;
        }
        if data.len() > control.length {
            Err(anyhow!(
                "Device returned too much data for control IN transfer (expected {}, got {})",
                control.length,
                data.len()
            ))?;
        }
        /* Return early if the transfer failed, no need for a status stage */
        if status != QemuUsbdevTransferStatus::Success {
            return Err(UsbError::TransferFailed(
                status,
                anyhow!("control IN data transfer failed"),
            ));
        }
        /* Status stage */
        let expected_id = self
            .send_transfer_out(
                control.addr,
                control.ep,
                /* zlp */ true,
                control.max_pkt_size,
                &[],
            )
            .maybe_context("Failed to send control IN status packet")?;
        let QemuUsbdevCompleteEvent { id, status, .. } = self
            .wait_complete()
            .maybe_context("Failed to receive control IN status")?;
        if status != QemuUsbdevTransferStatus::Success {
            return Err(UsbError::TransferFailed(
                status,
                anyhow!("control IN status transfer failed"),
            ));
        }
        if id != expected_id {
            Err(anyhow!(
                "Expected control IN status complete command ID with {expected_id:?}, got {id:?}"
            ))?;
        }
        Ok(data)
    }

    /// Perform a full control OUT transaction:
    /// - send a Setup
    /// - send a Transfer OUT (if any)
    /// - send a Transfer IN (status stage)
    /// - wait for status
    fn send_and_wait_control_out<'a>(&mut self, control: &ControlOut<'a>) -> UsbResult<()> {
        let expected_id = self
            .send_control_out(control)
            .context("Failed to send control OUT transfer")?;
        // Wait for data stage to complete if any.
        if let Some(expected_id) = expected_id {
            let QemuUsbdevCompleteEvent { id, status, .. } = self
                .wait_complete()
                .context("Failed to send control OUT data")?;
            if id != expected_id {
                Err(anyhow!(
                    "Expected control OUT data complete command ID with {expected_id:?}, got {id:?}"
                ))?;
            }
            /* Return early if the transfer failed, no need for a status stage */
            if status != QemuUsbdevTransferStatus::Success {
                return Err(UsbError::TransferFailed(
                    status,
                    anyhow!("control OUT data transfer failed"),
                ));
            }
        }
        /* Status stage */
        let expected_id = self
            .send_transfer_in(control.addr, control.ep, control.max_pkt_size, 0)
            .maybe_context("Failed to send control OUT status packet")?;
        let QemuUsbdevCompleteEvent { id, status, .. } = self
            .wait_complete()
            .maybe_context("Failed to receive control OUT status")?;
        if status != QemuUsbdevTransferStatus::Success {
            return Err(UsbError::TransferFailed(
                status,
                anyhow!("control OUT status transfer failed"),
            ));
        }
        if id != expected_id {
            Err(anyhow!(
                "Expected control OUT status complete command ID with {expected_id:?}, got {id:?}"
            ))?;
        }
        Ok(())
    }

    /// Perform a full enumeration sequence, retrieving the
    /// device and config descriptors, as well as assigning
    /// an address to the device.
    fn enumerate_device(&mut self) -> UsbResult<DeviceInfo> {
        // Send a reset to the device.
        let _ = self
            .send_packet(QemuUsbdevCmd::Reset, &[])
            .maybe_context("Failed to send RESET command")?;

        // Start a typical enumeration sequence by asking for the first 8 bytes
        // of the device descriptor.
        let trunc_dev_desc = self
            .send_and_wait_control_in(&ControlIn {
                addr: 0,
                ep: 0,
                req_type: Self::USB_REQ_TYPE_IN
                    | Self::USB_REQ_TYPE_STANDARD
                    | Self::USB_REQ_TYPE_DEVICE,
                req: Self::USB_GET_DESCRIPTOR,
                value: (Self::USB_DEVICE_DESCRIPTOR as u16) << 8,
                index: 0,
                length: Self::USB_FS_SAFE_PACKET_SIZE.into(),
                max_pkt_size: Self::USB_FS_SAFE_PACKET_SIZE,
            })
            .maybe_context("Failed to send GET_DESC(device, 8 bytes)")?;
        let max_packet_size = trunc_dev_desc[Self::USB_DEV_DESC_MAX_PACKET_SIZE_OFFSET] as u16;
        log::info!("USB Host: device report a maximum packet size of {max_packet_size} on EP0");
        // TODO sanity check max packet size

        // Assign an address to the device.
        let address = 42; // Arbitrary number.
        self.send_and_wait_control_out(&ControlOut {
            addr: 0,
            ep: 0,
            req_type: Self::USB_REQ_TYPE_OUT
                | Self::USB_REQ_TYPE_STANDARD
                | Self::USB_REQ_TYPE_DEVICE,
            req: Self::USB_SET_ADDRESS,
            value: address as u16,
            index: 0,
            max_pkt_size: max_packet_size,
            data: &[],
        })
        .maybe_context("Failed to send SET_ADDRESS")?;
        log::info!("USB Host: device accepted address {address:?}");

        // Give time to the device to update its address.
        std::thread::sleep(Duration::from_millis(Self::SET_ADDRESS_WAIT_DELAY_MS));

        // Retrieve the full device descriptor.
        let dev_desc = self
            .send_and_wait_control_in(&ControlIn {
                addr: address,
                ep: 0,
                req_type: Self::USB_REQ_TYPE_IN
                    | Self::USB_REQ_TYPE_STANDARD
                    | Self::USB_REQ_TYPE_DEVICE,
                req: Self::USB_GET_DESCRIPTOR,
                value: (Self::USB_DEVICE_DESCRIPTOR as u16) << 8,
                index: 0,
                length: size_of::<desc::DeviceDescriptor>(),
                max_pkt_size: max_packet_size,
            })
            .maybe_context("Failed to send GET_DESC(device, all bytes)")?;
        // Extract number of configurations.
        let num_config = desc::DeviceDescriptor::ref_from_bytes(&dev_desc)
            .map_err(|_err| anyhow!("Cannot parse device descriptor"))?
            .num_config;

        // Retrieve all configurations descriptors.
        let mut configurations = Vec::new();
        let mut first_config_val = None;
        for config_idx in 0..num_config {
            // Retrieve just the configuration descriptor first.
            let config_desc = self
                .send_and_wait_control_in(&ControlIn {
                    addr: address,
                    ep: 0,
                    req_type: Self::USB_REQ_TYPE_IN
                        | Self::USB_REQ_TYPE_STANDARD
                        | Self::USB_REQ_TYPE_DEVICE,
                    req: Self::USB_GET_DESCRIPTOR,
                    value: (Self::USB_CONFIG_DESCRIPTOR as u16) << 8 | config_idx as u16,
                    index: 0,
                    length: size_of::<desc::ConfigurationDescriptor>(),
                    max_pkt_size: max_packet_size,
                })
                .maybe_context(format!("Failed to send GET_DESC(config desc {config_idx})"))?;
            // Parse and extract the size of the full configuration.
            let parsed_desc = desc::ConfigurationDescriptor::ref_from_bytes(&config_desc)
                .map_err(|_err| anyhow!("Cannot parse config descriptor"))?;
            let tot_len = parsed_desc.tot_length;
            // Remember the configuration value for later.
            if first_config_val.is_none() {
                first_config_val = Some(parsed_desc.config_val);
            }
            // Retrieve full configuration.
            let full_config = self
                .send_and_wait_control_in(&ControlIn {
                    addr: address,
                    ep: 0,
                    req_type: Self::USB_REQ_TYPE_IN
                        | Self::USB_REQ_TYPE_STANDARD
                        | Self::USB_REQ_TYPE_DEVICE,
                    req: Self::USB_GET_DESCRIPTOR,
                    value: (Self::USB_CONFIG_DESCRIPTOR as u16) << 8 | config_idx as u16,
                    index: 0,
                    length: tot_len.into(),
                    max_pkt_size: max_packet_size,
                })
                .maybe_context(format!("Failed to send GET_DESC(full config {config_idx})"))?;
            configurations.push(full_config);
        }

        // Set the first available configuration.
        if let Some(first_config_val) = first_config_val {
            self.send_and_wait_control_out(&ControlOut {
                addr: address,
                ep: 0,
                req_type: Self::USB_REQ_TYPE_OUT
                    | Self::USB_REQ_TYPE_STANDARD
                    | Self::USB_REQ_TYPE_DEVICE,
                req: Self::USB_SET_CONFIGURATION,
                value: first_config_val as u16,
                index: 0,
                max_pkt_size: max_packet_size,
                data: &[],
            })
            .maybe_context("Failed to send SET_CONFIGURATION")?;
        } else {
            log::error!("USB host: device has no configurations")
        }
        log::info!("USB Host: device configured");

        Ok(DeviceInfo {
            dev_desc,
            address,
            configurations,
        })
    }

    /// This thread simulates a USB host. It can react to events sent by otlib
    /// over the channel.
    fn run(&mut self) -> UsbResult<()> {
        log::debug!("USB host: thread started");
        // We spawn a thread just to listen to events sent by QEMU USBDEV.
        // Those will be sent to the same channel otlib uses to gives us
        // requests.

        let usbdev_for_reader = self
            .usbdev
            .try_clone_native()
            .expect("Could not clone TTYPort for reading");
        let channel_send_for_reader = self.channel_send.clone();
        thread::spawn(move || {
            if let Err(res) =
                Self::host_qemu_reader_thread(usbdev_for_reader, channel_send_for_reader)
            {
                // Ignore errors coming for the mpsc channel because they indicate that
                // the host thread shut down and the reader couldn't send a message.
                match res.downcast::<mpsc::SendError<HostChannelEvent>>() {
                    Ok(_) => (),
                    Err(err) => log::error!("QEMU reader failed with error: {err:?}"),
                }
            }
        });

        // Send HELLO.
        let id = self
            .send_hello()
            .maybe_context("Failed to send HELLO packet")?;
        // Expect HELLO back.
        let hello = self
            .wait_hello(id)
            .maybe_context("Failed waiting for an HELLO packet")?;
        log::info!(
            "USB host: device is using protocol version {}.{}",
            hello.major_version,
            hello.minor_version
        );

        // Power on VBUS.
        let _ = self
            .send_packet(QemuUsbdevCmd::VbusOn, &[])
            .maybe_context("Failed to send VBUS_ON command")?;

        loop {
            // Wait for device to connect.
            let _id = self
                .wait_connect()
                .context("Failed while waiting for a device to connect")?;

            log::info!("USB Host: device connected");

            // Perform enumeration and get back the descriptors.
            let dev_info = match self.enumerate_device() {
                Err(UsbError::Shutdown) => return Ok(()),
                Err(UsbError::Disconnected) => {
                    log::info!("USB Host: device disconnected");
                    continue;
                }
                Err(err) => {
                    log::error!("USB host: failed to enumerate device: {err:?}");
                    continue;
                }
                Ok(dev_info) => dev_info,
            };
            log::info!("USB Host: device configured: {dev_info:?}");

            break;
        }

        Ok(())
    }

    fn blocking_read_exact<T: Read>(read: &mut T, buf: &mut [u8]) -> anyhow::Result<()> {
        let mut pos = 0usize;
        while pos < buf.len() {
            match read.read(&mut buf[pos..]) {
                Ok(amount) => pos += amount,
                Err(err)
                    if err.kind() == std::io::ErrorKind::TimedOut
                        || err.kind() == std::io::ErrorKind::Interrupted =>
                {
                    continue;
                }
                err => {
                    err?;
                }
            }
        }
        Ok(())
    }

    /// This thread is responsible for receiving messages from QEMU (following the usbdev
    /// protocol). When done, it sends a message to the virtual host channel with the content.
    fn host_qemu_reader_thread(
        mut usbdev: TTYPort,
        channel_send: mpsc::Sender<HostChannelEvent>,
    ) -> anyhow::Result<()> {
        log::debug!("USB host: QEMU reader thread started");

        loop {
            // Wait for a header.
            let mut hdr = [0u8; size_of::<QemuUsbdevPacketHeader>()];
            Self::blocking_read_exact(&mut usbdev, &mut hdr)
                .context("Failed to read a packet header from QEMU")?;
            let hdr = QemuUsbdevPacketHeader::ref_from_bytes(&hdr).unwrap();
            // TODO sanity check the size

            let mut data = vec![0; Into::<u32>::into(hdr.size) as usize];
            Self::blocking_read_exact(&mut usbdev, &mut data)
                .context("Failed to read a packet data from QEMU")?;

            channel_send
                .send(HostChannelEvent::QemuMessage {
                    cmd: hdr.command.into(),
                    id: hdr.id.into(),
                    data,
                })
                .context("Failed to send a message to the host thread")?;
        }
    }
}
