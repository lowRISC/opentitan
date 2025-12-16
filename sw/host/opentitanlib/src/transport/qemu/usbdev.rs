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
use std::time::{Duration, Instant};
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

/// Events sent by otlib to the virtual host thread.
#[derive(Debug)]
enum HostChannelEvent {
    /// A message was sent by QEMU to the host.
    QemuMessage { cmd: u32, id: u32, data: Vec<u8> },
    /// Request information about the currently plugged device.
    /// The information is immediately sent back over the channel.
    GetDeviceInfo {
        answer: mpsc::Sender<Option<DeviceInfo>>,
    },
    /// Request to be notified on any device change (connection or disconnection).
    NotifyDeviceChange { answer: mpsc::Sender<()> },
}

/// Minimal virtual USB host to drive the QEMU usbdev.
pub struct QemuUsbHost {
    /// Sender to notify the virtual host thread of various events
    /// from the otlib side.
    host_channel: mpsc::Sender<HostChannelEvent>,
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

        QemuUsbHost { host_channel: send }
    }

    /// Try to obtain information about the QEMU device connected.
    /// This is non-blocking.
    fn device_info(&self) -> UsbResult<Option<DeviceInfo>> {
        let (send, recv) = mpsc::channel();
        self.host_channel
            .send(HostChannelEvent::GetDeviceInfo { answer: send })?;
        Ok(recv.recv()?)
    }

    /// Wait for a device change or a timeout. Return an error if no
    /// changes occurred within the time limit.
    fn wait_device_change(&self, timeout: Duration) -> UsbResult<()> {
        let (send, recv) = mpsc::channel();
        self.host_channel
            .send(HostChannelEvent::NotifyDeviceChange { answer: send })?;
        Ok(recv.recv_timeout(timeout)?)
    }

    fn device_matches_filter(
        &self,
        device: &QemuUsbDevice,
        usb_vid_pid: Option<(u16, u16)>,
        usb_protocol: Option<(u8, u8, u8)>,
        usb_serial: Option<&str>,
    ) -> UsbResult<bool> {
        // Parsing cannot fail because it was parsed during enumeration.
        if let Some((usb_vid, usb_pid)) = usb_vid_pid {
            if device.get_vendor_id() != usb_vid || device.get_product_id() != usb_pid {
                return Ok(false);
            }
        }

        if let Some((class, subclass, protocol)) = usb_protocol {
            // Failure should never occur to get the active descriptor since
            // it is cached.
            let config = device.active_configuration()?;
            let mut found = false;
            for intf in config.interface_alt_settings() {
                if let Ok(desc) = intf.descriptor() {
                    if desc.class == class && desc.subclass == subclass && desc.protocol == protocol
                    {
                        found = true;
                    }
                }
            }
            if !found {
                return Ok(false);
            }
        }

        if let Some(_usb_serial) = usb_serial {
            log::error!("matching by serial number is not implemented yet");
        }
        Ok(true)
    }

    fn device_by_filter_with_timeout(
        &self,
        usb_vid_pid: Option<(u16, u16)>,
        usb_protocol: Option<(u8, u8, u8)>,
        usb_serial: Option<&str>,
        timeout: Duration,
    ) -> anyhow::Result<Box<dyn UsbDevice>> {
        let deadline = Instant::now() + timeout;

        loop {
            let now = Instant::now();
            if now > deadline {
                return Err(anyhow!("no device found"));
            }
            if let Some(dev_info) = self.device_info()? {
                let dev = QemuUsbDevice::new(self, dev_info);
                match self.device_matches_filter(&dev, usb_vid_pid, usb_protocol, usb_serial) {
                    Ok(true) => return Ok(Box::new(dev)),
                    Ok(false) => (),
                    Err(err) => {
                        log::error!("{err:?}");
                    }
                }
            }
            // If the device did not match our expectation, wait until
            // a new device shows up.
            log::info!("wait for device change");
            self.wait_device_change(deadline - now)?;
        }
    }
}

impl OtUsbContext for QemuUsbHost {
    fn device_by_id_with_timeout(
        &self,
        usb_vid: u16,
        usb_pid: u16,
        usb_serial: Option<&str>,
        timeout: Duration,
    ) -> anyhow::Result<Box<dyn UsbDevice>> {
        self.device_by_filter_with_timeout(Some((usb_vid, usb_pid)), None, usb_serial, timeout)
    }

    fn device_by_interface_with_timeout(
        &self,
        class: u8,
        subclass: u8,
        protocol: u8,
        usb_serial: Option<&str>,
        timeout: Duration,
    ) -> anyhow::Result<Box<dyn UsbDevice>> {
        self.device_by_filter_with_timeout(
            None,
            Some((class, subclass, protocol)),
            usb_serial,
            timeout,
        )
    }
}

#[derive(Debug)]
struct QemuUsbDevice {
    dev_info: DeviceInfo,
    /// Active configuration *index*.
    active_cfg_idx: usize,
    timeout: Duration,
}

impl QemuUsbDevice {
    fn new(_host: &QemuUsbHost, dev_info: DeviceInfo) -> Self {
        QemuUsbDevice {
            dev_info,
            // The host always set the first available configuration.
            active_cfg_idx: 0,
            // Operations should be reasonably fast with QEMU.
            timeout: Duration::from_millis(500),
        }
    }
}

impl UsbDevice for QemuUsbDevice {
    fn get_vendor_id(&self) -> u16 {
        // This cannot fail, the device descriptor was parsed during enumeration.
        desc::DeviceDescriptor::ref_from_bytes(&self.dev_info.dev_desc)
            .unwrap()
            .vendor_id
            .into()
    }

    /// Return the PID of the device.
    fn get_product_id(&self) -> u16 {
        // This cannot fail, the device descriptor was parsed during enumeration.
        desc::DeviceDescriptor::ref_from_bytes(&self.dev_info.dev_desc)
            .unwrap()
            .product_id
            .into()
    }

    /// Gets the serial number of the device.
    fn get_serial_number(&self) -> Option<&str> {
        // TODO
        None
    }

    /// Set the active configuration.
    fn set_active_configuration(&self, _config: u8) -> anyhow::Result<()> {
        anyhow::bail!("unimplemented set_active_configuration");
    }

    /// Claim an interface for use with the kernel.
    fn claim_interface(&self, _iface: u8) -> anyhow::Result<()> {
        Ok(())
    }

    /// Release a previously claimed interface to the kernel.
    fn release_interface(&self, _iface: u8) -> anyhow::Result<()> {
        Ok(())
    }

    /// Set an interface alternate setting.
    fn set_alternate_setting(&self, _iface: u8, _setting: u8) -> anyhow::Result<()> {
        anyhow::bail!("unimplemented set_alternate_setting");
    }

    /// Check whether a kernel driver currently controls the device.
    fn kernel_driver_active(&self, _iface: u8) -> anyhow::Result<bool> {
        Ok(false)
    }

    /// Detach the kernel driver from the device.
    fn detach_kernel_driver(&self, _iface: u8) -> anyhow::Result<()> {
        Ok(())
    }

    /// Attach the kernel driver to the device.
    fn attach_kernel_driver(&self, _iface: u8) -> anyhow::Result<()> {
        Ok(())
    }

    /// Return the currently active configuration's descriptor.
    fn active_configuration(&self) -> anyhow::Result<desc::Configuration> {
        Ok(desc::Configuration::new(
            &self.dev_info.configurations[self.active_cfg_idx],
        ))
    }

    /// Return the device's bus number.
    fn bus_number(&self) -> u8 {
        0
    }

    /// Return the sequence of port numbers from the root down to the device.
    fn port_numbers(&self) -> anyhow::Result<Vec<u8>> {
        Ok(vec![0])
    }

    /// Return a string descriptor in ASCII.
    fn read_string_descriptor_ascii(&self, _idx: u8) -> anyhow::Result<String> {
        anyhow::bail!("unimplemented read_string_descriptor_ascii");
    }

    /// Reset the device.
    ///
    /// Note that this UsbDevice handle will most likely become invalid
    /// after resetting the device and a new one has to be obtained.
    fn reset(&self) -> anyhow::Result<()> {
        anyhow::bail!("unimplemented reset");
    }

    /// Get the default timeout for operations.
    fn get_timeout(&self) -> Duration {
        self.timeout
    }

    /// Issue a USB control request with optional host-to-device data.
    fn write_control_timeout(
        &self,
        _request_type: u8,
        _request: u8,
        _value: u16,
        _index: u16,
        _buf: &[u8],
        _timeout: Duration,
    ) -> anyhow::Result<usize> {
        anyhow::bail!("unimplemented write_control_timeout");
    }

    /// Issue a USB control request with optional device-to-host data.
    fn read_control_timeout(
        &self,
        _request_type: u8,
        _request: u8,
        _value: u16,
        _index: u16,
        _buf: &mut [u8],
        _timeout: Duration,
    ) -> anyhow::Result<usize> {
        anyhow::bail!("unimplemented write_control_timeout");
    }

    /// Read bulk data bytes to given USB endpoint.
    fn read_bulk_timeout(
        &self,
        _endpoint: u8,
        _data: &mut [u8],
        _timeout: Duration,
    ) -> anyhow::Result<usize> {
        anyhow::bail!("unimplemented");
    }

    /// Write bulk data bytes to given USB endpoint.
    fn write_bulk_timeout(
        &self,
        _endpoint: u8,
        _data: &[u8],
        _timeout: Duration,
    ) -> anyhow::Result<usize> {
        anyhow::bail!("unimplemented");
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
    Cancel,
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

/// USBDEV cancel payload, see QEMU documentation.
#[derive(Clone, IntoBytes, KnownLayout, Immutable, Unaligned)]
#[repr(C)]
pub struct QemuUsbdevCancelPayload {
    transfer_id: little_endian::U32,
}

/// Represents a packet ID.
#[derive(Debug, Clone, Copy, Eq, Hash, PartialEq)]
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
    /// Operation timed out
    #[error("Operation timed out")]
    Timeout,
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

impl From<mpsc::SendError<HostChannelEvent>> for UsbError {
    fn from(_value: mpsc::SendError<HostChannelEvent>) -> UsbError {
        UsbError::Shutdown
    }
}

impl From<mpsc::RecvError> for UsbError {
    fn from(_value: mpsc::RecvError) -> UsbError {
        UsbError::Shutdown
    }
}

impl From<mpsc::RecvTimeoutError> for UsbError {
    fn from(value: mpsc::RecvTimeoutError) -> UsbError {
        match value {
            mpsc::RecvTimeoutError::Timeout => UsbError::Timeout,
            mpsc::RecvTimeoutError::Disconnected => UsbError::Shutdown,
        }
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

/// This structure represents an enumerated and configured device.
#[derive(Clone, Debug)]
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

/// This structure represents an enumerated and configured device.
#[derive(Clone, Debug)]
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
    /// List of pending channels that should be notified on a
    /// device change.
    pending_dev_changes: Vec<mpsc::Sender<()>>,
}

impl QemuHostThread {
    const USBDEV_HELLO_MAGIC: [u8; 4] = *b"UDCX";
    const USBDEV_HELLO_MAJOR: u16 = 1;
    const USBDEV_HELLO_MINOR: u16 = 0;

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
            pending_dev_changes: Vec::new(),
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

    fn _send_cancel(&mut self, xfer_id: PacketId) -> UsbResult<PacketId> {
        let cancel_cmd = QemuUsbdevCancelPayload {
            transfer_id: xfer_id.0.into(),
        };

        self.send_packet(QemuUsbdevCmd::Cancel, &[cancel_cmd.as_bytes()])
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
            ep | USBDEV_TRANSFER_EP_IN,
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
    /// wrong. Other requests will be handled assuming the context of a device enumerating.
    fn wait_qemu_event(&mut self) -> UsbResult<QemuUsbdevEvent> {
        loop {
            let Ok(event) = self.channel_recv.recv() else {
                return Err(UsbError::Shutdown);
            };
            match event {
                HostChannelEvent::QemuMessage { cmd, id, data } => {
                    let cmd = QemuUsbdevCmd::try_from(cmd)
                        .with_context(|| format!("Unknown command {cmd} from USBDEV"))?;
                    return Ok(QemuUsbdevEvent {
                        cmd,
                        id: PacketId(id),
                        data,
                    });
                }
                HostChannelEvent::GetDeviceInfo { answer } => {
                    // There is no device connected. Ignore errors (ie the other end disconnected).
                    let _ = answer.send(None);
                }
                HostChannelEvent::NotifyDeviceChange { answer } => {
                    self.pending_dev_changes.push(answer)
                }
            }
        }
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
                req_type: USB_REQ_TYPE_IN | USB_REQ_TYPE_STANDARD | USB_REQ_TYPE_DEVICE,
                req: USB_GET_DESCRIPTOR,
                value: (USB_DEVICE_DESCRIPTOR as u16) << 8,
                index: 0,
                length: USB_FS_SAFE_PACKET_SIZE.into(),
                max_pkt_size: USB_FS_SAFE_PACKET_SIZE,
            })
            .maybe_context("Failed to send GET_DESC(device, 8 bytes)")?;
        let max_packet_size = trunc_dev_desc[USB_DEV_DESC_MAX_PACKET_SIZE_OFFSET] as u16;
        log::info!("USB Host: device report a maximum packet size of {max_packet_size} on EP0");
        // TODO sanity check max packet size

        // Assign an address to the device.
        let address = 42; // Arbitrary number.
        self.send_and_wait_control_out(&ControlOut {
            addr: 0,
            ep: 0,
            req_type: USB_REQ_TYPE_OUT | USB_REQ_TYPE_STANDARD | USB_REQ_TYPE_DEVICE,
            req: USB_SET_ADDRESS,
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
                req_type: USB_REQ_TYPE_IN | USB_REQ_TYPE_STANDARD | USB_REQ_TYPE_DEVICE,
                req: USB_GET_DESCRIPTOR,
                value: (USB_DEVICE_DESCRIPTOR as u16) << 8,
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
                    req_type: USB_REQ_TYPE_IN | USB_REQ_TYPE_STANDARD | USB_REQ_TYPE_DEVICE,
                    req: USB_GET_DESCRIPTOR,
                    value: (USB_CONFIG_DESCRIPTOR as u16) << 8 | config_idx as u16,
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
                    req_type: USB_REQ_TYPE_IN | USB_REQ_TYPE_STANDARD | USB_REQ_TYPE_DEVICE,
                    req: USB_GET_DESCRIPTOR,
                    value: (USB_CONFIG_DESCRIPTOR as u16) << 8 | config_idx as u16,
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
                req_type: USB_REQ_TYPE_OUT | USB_REQ_TYPE_STANDARD | USB_REQ_TYPE_DEVICE,
                req: USB_SET_CONFIGURATION,
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

    /// Serve requests for the device until it disconnects .
    fn serve_device_requests(&mut self, dev_info: &DeviceInfo) -> UsbResult<()> {
        loop {
            let Ok(event) = self.channel_recv.recv() else {
                return Err(UsbError::Shutdown);
            };
            match event {
                HostChannelEvent::QemuMessage { cmd, id, data } => {
                    let cmd = QemuUsbdevCmd::try_from(cmd)
                        .with_context(|| format!("Unknown command {cmd} from USBDEV"))?;
                    match cmd {
                        QemuUsbdevCmd::Disconnect => return Err(UsbError::Disconnected),
                        cmd => {
                            log::error!(
                                "ignoring unexpected QEMU event: {cmd:?}, id={id}, data={data:?}"
                            );
                        }
                    }
                }
                HostChannelEvent::GetDeviceInfo { answer } => {
                    // Ignore errors (ie the other end disconnected).
                    let _ = answer.send(Some(dev_info.clone()));
                }
                HostChannelEvent::NotifyDeviceChange { answer } => {
                    self.pending_dev_changes.push(answer)
                }
            }
        }
    }

    fn notify_device_change(&mut self) {
        for send in &self.pending_dev_changes {
            // Ignore errors (receiver might have disconnected after a timeout).
            let _ = send.send(());
        }
        self.pending_dev_changes.clear();
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

            self.notify_device_change();

            // Handle messages until the device disconnects.
            match self.serve_device_requests(&dev_info) {
                Err(UsbError::Shutdown) => return Ok(()),
                Err(UsbError::Disconnected) | Ok(()) => {
                    log::info!("USB Host: device disconnected");
                }
                Err(err) => {
                    log::error!("USB host: an error occurred: {err:?}");
                    // Pretend that device has disconnected.
                }
            }
            self.notify_device_change();
        }
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
