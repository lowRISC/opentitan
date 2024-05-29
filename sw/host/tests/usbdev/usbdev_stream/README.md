# Host-side streaming software

To verify the USB device (USBDEV) with a physical USB host requires special-purpose software to
communicate with the device, checking all of the data transferred. This `stream_test` program forms
the host-side component of the verification effort, complementing the following device-side tests:

- usbdev_stream_test
  - Device-side software that streams Bulk Transfer data to/from multiple endpoints, generating the
    source data using a LFSR, and then checking the data returned by the USB host against the
    device-side predictions.

- usbdev_iso_test
  - Derived from `usbdev_stream_test` and sharing a common body of code, this test employs
    Isochronous transfers instead of Bulk Transfers. Isochronous Transfers have the important
    distinction that the packet stream is inherently unreliable and there is no acknowledgement or
    retrying of bad packets for Isochronous Transfers. Instead, this transfer type prioritizes the
    timely delivery of new data over any retrying and error detection.
  - Since the USB guarantees the bandwidth available to Isochronous endpoints, it is not possible
    to implement the full complement of 12 supported endpoints in this test, and instead only
    four concurrent streams are used. This allows the test to operate with a number of intervening
    hubs between the USB host and device, without suffering from a failure to guarantee the
    bandwidth requirements.

- usbdev_mixed_test
  - This test is more comprehensive than the above two tests in that it tests a combination of
    Bulk Transfers, Interrupt Transfers and Isochronous Transfers concurrently.

This host-side component typically uses `libusb` in order to verify all of the four Transfer Types
supported by the USB:

- Bulk Transfers
- Isochronous Transfers
- Interrupt Transfers
- Control Transfers

The `stream_test` program is also able to communicate over serial port connections using the
regular file I/O API of the OS. If `libusb` is not available on the host platform, then the
host-side software may be built with the macro 'STREAMTEST_LIBUSB' undefined or set to 0, allowing
direct serial port access to be used on other Linux or Linux-like hosts.

## Device identification and the 'USBDevice' class

When the 'stream_test' software has been built with `libusb` support, it is capable of locating and
identifying the USB device automatically by searching for a connected device having the expected
Vendor and Product IDs. If the device is connected and the device-side test software has configured
the USB device in response to the configuration requests from the USB host, it should be detected
by `stream_test`, and testing will commence.

If there is a connection issue or the configuration sequence does not completely successfully,
there may be some useful diagnostic information available via `sudo dmesg -w` for a Linux host.

```
[101210.703949] usb 3-9.3: new full-speed USB device number 78 using xhci_hcd
[101210.854843] usb 3-9.3: New USB device found, idVendor=18d1, idProduct=503a, bcdDevice= 1.00
[101210.854862] usb 3-9.3: New USB device strings: Mfr=0, Product=0, SerialNumber=0
[101210.921072] usb_serial_simple 3-9.3:1.0: google converter detected
[101210.921480] usb 3-9.3: google converter now attached to ttyUSB0
...
```

The start of the normal device identification and configuration is shown above. The
`usbdev_stream_test` test software presents the device in a manner that makes it suitable for
use by the 'usb-serial-simple' driver for Bulk Transfer communications. This makes an endpoint pair
behave two reliable, unidirectional, serial byte streams without any requirement for configuration
commands, flow control or handshaking etc.

## USBDPI model

Since verification of USBDEV is also performed using DV simulation (at both chip- and block-level)
and Verilator top-level simulation, there is a counterpart implementation of the 'stream_test'
functionality within the USBDPI model. This employs the same, umodified device-side tests and
offers greater control over the USB traffic than may be achieved using a physical host.

## Test Descriptor

Having located the USBDEV using `libusb` the host-side code will attempt to read a test descriptor
from the device-side test code using a 'Vendor Specific' Control Transfer. This is a bespoke
command that is interpreted by the device-side test software, and which returns a description of
the functionality required of the streaming code, including the number of streams to be tested
concurrently, and the transfer type of each of the streams.

## Stream signatures

The host-side code initiates communications with each of the device-side endpoints by claiming the
interface for exclusive use and performing an initial read from the IN endpoint. The start of the
received data stream is expected to consist of a stream signature that specifies the properties
of the stream, including the initial value of the LFSR used to generate the pseudo-random byte
stream.

## LFSR-based data generation

The device-side test software has one LFSR implementation for each of its streams, and uses these
to generate the byte streams. Since the host-side code is informed of the initial state of each LFSR
via the stream signatures, and employs the same algoriths, the host-side code may check the received
data for correctness and thus detect any transmission errors and signal integrity issues on the USB.

Having verified the received bytes against expectations using its own model of the device-side LFSR,
the host-side code in `stream_test` then combines each byte with the output from its own LFSR for
that stream, before sending the results stream back to the device. This resulting byte stream is
simply the bytewise XOR of the device-side LFSR output and the host-side LFSR output.

Upon receipt of data from the USB host, the device-side test software will check the received
data against its own prediction of the XOR of the two LFSR outputs, thus verifying the correct,
error-free transmission of data from host to device.

## Circular Buffer Implementation

Within the `USBDevStream` base class, from which the other stream types derive, there is an
implementation of a circular buffer using statically-allocated storage within the USBDevStream
instance itself. This is a relatively small buffer that keeps the byte stream flowing from and to
the device, without the need for additional data movement.

For the serial port implementation in 'USBDevSerial' this is a generalized byte stream with the
amount of data being received/transmitted having byte-level granularity. For the other stream
implementations the transfers are packet-based, in accordance with the interface exposed by
`libusb` and it is therefore necessary to anticipate the recept of a maximum-length packet,
since is the device-side test software that determines the individual, randomized sizes of the
packets, rather than the USB requests from the host.

To this end, in addition to the usual 'read' and 'write' indexes into the circular buffer
implementation, there is an 'end' index which tracks the current used size of the circular buffer,
allowing the buffer contents to wrap prematurely in the event that another maximum-length packet
cannot be accommodated contiguously.

## Special considerations for Isochronous streams

Since Isochronous Transfers prioritize the timely delivery or recent data over the reliable,
error-free delivery of all data, Isochronous packets are subject to be dropped from the byte
stream at any point, but particularly in the OUT direction (host to device) since the device-side
software is running on much slower hardware than the host-side code. Additionally, the USB host
controls the USB so packets that are requested will usually have sufficient space available
for storage.

Packets transmitted to the USB device may be dropped silently when there is no storage space
available, or in the event of data corruption occurring on the USB. As such the streaming code
on the device side populates the first part of each Isochronous packet with a stream signature
that indicates both the sequence number of the packet and the initial value of the device-side
LFSR for that packet. This allows the USB host to detect the disappearance of packets on the IN
side (device to host), and to run both its mirror of the device-side LFSR and its own host-side LFSR
forwards to resynchronize.

One further point to note regarding tests that employ Isochronous Transfers is that the host-side
`stream_test` code is unable to ascertain when all data has been transferred, because it receives
no guarantee that transmitted data has arrived at the USB device.

Since the device-side tests software is ultimately responsible for deciding the pass/fail status
of the test, the test framework on the host shall be expected to terminate the `stream_test` when
a verdict has been reached.

## Suspend/Resume testing

In addition to the normal streaming and checking operations of the `stream_test` software, it may
be used to exercise the Suspend/Resume behavior of the USB device. The USB device has a companion
module called `usbdev_aon_wake` that may be used to keep the bus alive and monitor events occurring
on the USB whilst most of the chip enters a lower power 'sleep' state.

In order for a Linux host to put a USB device to perform Suspend signaling, which indicates to the
device that it is presently not required to communicate and may enter a low power mode, all file
handles including those held by the `libusb` code must be closed.

To initiate a Suspend operation, the `stream_test` software will therefore temporarily cease the
scheduling of new transfers on any stream, and await the completion of existing transfers,
before then 'closing' the streams. Note that the USBDevStream instances remain extant, and that
their internal state remains intact for use after resuming; in particular, communication must
continue from the point at which the stream was suspended without packet loss.

After an appropriate interval in the Suspended state, `stream_test` will then invoke 'Resume()' on
each of the streams in turn, causing them to reestablish communication with the USBDEV. Each of
the streams continues from the point of suspension with all LFSR state and byte counts unmodified.

Note that it may prove necessary to run the OpenTitanTool test harness and the `stream_test`
host-side code on separate hosts to test this behavior meaningfully, because something within the
standard USB driver stack on a Linux host causes USB devices to be reawakened from their Suspended
state every few seconds, making it impossible to put the USBDEV into a low power sleep state for
any prolonged period.
