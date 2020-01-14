---
title: "Simple USB Full Speed Device IP Technical Specification"
---

# Overview



## Features

- USB Full-Speed (12Mbps) Device interface

- 2kbyte Interface buffer

- Up to 12 Endpoints (including required Endpoint 0)

- Support for USB packet size up to 64 bytes

- Support SETUP, IN and OUT transactions

- Support for Bulk, Control, Interrupt and Isochronous endpoints and transactions

- Initial version does not support Isochronous transfers larger than
  64 bytes (later extension)

- Streaming possible through software

- Interrupts for packet reception and transmission


## Description

The USB device module is a simple software-driven gneric USB device
interface for Full-Speed USB operation. The IP includes the physical
layer interface (switchable between regular 3.3V I/O pads, or a differential
USB transceiver), the low level USB protocol and a packet
buffer interface to the software.


## Compatibility

The USB device programming interface is not based on any existing
interface.


# Theory of Operations

A useful quick reference for USB Full-Speed is
[http://www.usbmadesimple.co.uk/ums_3.htm](http://www.usbmadesimple.co.uk/ums_3.htm)

The block diagram shows a high level view of the simple USB Device
including the main register access paths.

![Block Diagram](usbdev_block.svg "image_tooltip")


## Clocking

The USB Full-Speed interface runs at a 12MHz datarate. 
The interface runs at four times this and must be clocked from an accurate 48MHz clock source. 
The USB specification for a Full-Speed device requires the average bit-rate is 12Mbps +/- 0.25%, so the clock needs to support maximum error of 2,500ppm.  
The maximum allowable integrated jitter is +/- 1ns over 1 to 7 bit-periods.

Control transfers pass through asynchronous FIFOs or have a ready bit
synchronized across the clock domain boundary. A dual-port
asynchronous buffer SRAM is used for data transfers between the bus
clock and USB clock domains.

## USB Interface Pins

The interface pin table summarizes the external pins.


|External Pin|Internal Signal|Notes|
|------------|---------------|-----|
|USB D+, USB D-|usb_d_i, usb_dp_i, usb_dn_i, usb_d_o, usb_se0_o|Interface to a differential USB transceiver. This interface can be selected by writing 1 to {{< regref "phy_config.rx_differential_mode" >}} and {{< regref "phy_config.tx_differential_mode" >}}.|
|USB D+, USB D-|usb_dp_i, usb_dn_i, usb_dp_o, usb_dn_o|Single-ended interface to regular IO cells. This interface can be used for prototyping on an FPGA, but will probably not be USB compliant. This interface can be selected by writing 0 to {{< regref "phy_config.rx_differential_mode" >}} and {{< regref "phy_config.tx_differential_mode" >}}.|
||usb_oe_o|Enable driving the external pins.|
|[usb_pullup]|usb_pullup_o|When the usb_pullup_o asserts a 1.5k pullup resistor should be connected to D+. This can be done inside the chip or with an external pin. A permanently connected resistor can also be used.|
|[TX Mode]|tx_mode_se_o|Indicates the selected TX mode. 1 corresponds to single-ended operation.|
|usb_sense|usb_sense_i|The sense pin indicates the presence of VBUS from the host.|

The USB 2.0 Full Speed specification uses a bidirectional serial interface that can be implemented with pseudo-differential 3.3V GPIO pins and an oversampling receiver for recovery of the bitstream and clock alignment.
The IP interface for the D+ and D- pins is presented using a pair of transmit signals, a pair of receive signals and a transmit enable.
External to the IP these should be combined to drive the pins when transmit is enabled and receive when transmit is not enabled.
Using standard 3.3V I/O pads allows use on most FPGAs although the drive strength and series termination resistors may need to be adjusted to meet the USB signal eye.
On a Xilinx Artix-7 (and less well tested Spartan-7) part, setting the driver to the 8mA, FAST setting seems to work well with a 22R series termination (and with a 0R series termination).

Alternatively, a dedicated USB transceiver can be used. 
This is required for USB compliance. 
Examples for such a transceiver are the USB1T11A or USB1T20. 
In this case differential signaling should be used for better receive sensitivity and lower transmit jitter.

A Full-Speed device identifies itself by providing a 1.5k pullup
resistor (to 3.3V) on the D+ line. The IP block produces a signal
usb_pullup that is asserted when this resistor should be
presented. This signal will be asserted whenever the interface is
enabled. In an FPGA implementation this signal can drive a 3.3V output
pin that is driven high when the signal is asserted and set high
impedance when the signal is deasserted, and the output pin used to
drive a 1.5k resistor connected on the board to the D+
line. Alternatively, it can be used to enable an internal 1.5k pullup
on the D+ pin.

The USB Host will identify itself to the device by enabling the 5V
VBUS power. It may do a hard reset of a port by removing and
reasserting VBUS (the Linux driver will do this when it finds a port
in an inconsistent state or a port that generates errors during
enumeration). The IP detects VBUS through the usb_sense pin. This pin
is always an input and should be externally connected to detect the
state of the VBUS. Note that this may require a resistor divider or
(for USB-C where VBUS can be up to 20V) active level translation to an
acceptable voltage for the input pin.

{{< hwcfg "hw/ip/usbdev/data/usbdev.hjson" >}}

## USB Link State

The USB link has a number of states. 
These are detected and reported in {{< regref "usbstat.link_state" >}} and state changes are reported using interrupts. 
The FSM implements a subset of the USB device state diagram shown in Figure 9-1 of the USB 2.0 specification.

|State| Description |
|-----|-------------|
|Disconnected | The link is disconnected. This is signalled when the VBUS is not driven by the host, which results in the sense input pin being low. An interrupt is raised on entering this state.|
|Powered| The device has been powered as VBUS is being driven by the host, but has not been reset yet. The link is reset whenever the D+ and D- are both low (an SE0 condition) for an extended period. The host will assert reset for a minumum of 10ms, but the USB specification allows the device to detect and respond to a reset after 2.5us. The implementation here will report the reset state and raise an interrupt when the link is in SE0 for 3us.|
|Powered Suspend| The link is suspended when at idle (a J condition) for more than 3ms. An interrupt is generated when the suspend is detected and a resume interrupt is generated when the link exits the suspend state. This state is entered, if the device has not been reset yet.|
|Active| The link is active when it is running normally|
|Suspened| Similar to 'Powered Suspend', but the device was in the active state before being suspended.|

|Link Events| Description |
|-----------|-------------|
|Disconnect| VBUS has been lost. |
|Link Reset| The link has been in the SE0 state for 3us.|
|Link Suspend| The link has been in the J state for more than 3ms, upon which we have to enter the suspend state.|
|Link Resume| The link has been driven to a non-J state after being in suspend.|
|Host Lost| The host lost interrupt will be signalled if the link is active but a start of frame has not been received from the host in 4.096ms. The host is required to send a SOF every 1ms. This is not an expected condition.|


## USB Protocol Engine

The USB 2.0 Full Speed Protocol Engine is provided by the common USB
interface code and is not part of this module.

At the lowest level of the USB stack the transmit bitstream is serialized, converted to NRZI encoding with bit-stuffing and sent to the transmitter. 
The received bitstream is recovered, clock aligned and decoded and has bit-stuffing removed. 
The recovered clock alignment is used for transmission.

The higher level protocol engine forms the bitstream into packets,
performs CRC checking and recognizes IN, OUT and SETUP
transactions. These are presented without buffering to this module
which must accept or provide data when requested. The protocol engine
may cancel a transaction because of a bad CRC or request a retry if an
ACK was not received.

## Buffer Interface

A 2k Byte SRAM is used to hold data between the system and the USB
interface. This is divided up into 32 buffers each containing 64
bytes. This is an asynchronous dual-port SRAM with the software
accessing from the bus clock domain and the USB interface accessing
from the USB 48MHz clock domain.

The 64 byte size for the buffers satisfies the maximum USB packet size
for a Full Speed interface for Control transfers (max may be 8, 16, 32
or 64 bytes), Bulk Transfers (max is 64 bytes) and Interrupt transfers
(max is 64 bytes). It is small for Isochronous transfers (which have a
max of 1023 bytes) and the interface will need extending for high rate
isochronous use (would probably allow up to 8 or 16 buffers to be
aggregated as the isoc buffer).

The software provides buffers for packet reception through a 4-entry
available-buffer FIFO. (More study needed but 4 seems about right: one
just returned to software, one being filled, one ready to be filled
and one for luck.) The {{< regref "RxEnable" >}} register is used to indicate which
endpoints will accept data from the host using SETUP or OUT
transactions. When a packet is transferred from the host to the device
(using an OUT or SETUP transaction) and reception of that type of
transaction is enabled for the requested endpoint, the next receive
buffer is pulled from the FIFO and will be filled with the data from
the packet. If the packet is correctly received then an ACK is
returned to the host and the buffer number, the packet size, an
out/setup flag and the endpoint number are passed back to software
using the receive FIFO and a pkt_received interrupt raised. The driver
should immediately provide a free buffer for future reception by
writing its buffer number to the available-buffer FIFO, then can
process the packet and eventually return the received buffer to the
free pool. This allows streaming on a single endpoint or across a
number of endpoints. If the packets cannot be consumed at the rate
they are received then software can implement selective flow-control
by disabling OUT or SETUP transactions for a particular endpoint,
which will result in a request to that endpoint being NACKed. In the
unfortunate event that the available-buffer FIFO is empty or receive
FIFO is full then all OUT/SETUP transactions are NACKed.

To send data to the host in response to an IN transaction the software
writes the data into a free buffer and writes the buffer number, data
length and a ready flag to the {{< regref "configin" >}} register for the endpoint
that the data is from. When the host next does an IN transaction to
that endpoint the data will be sent from the buffer. On receipt of the
ACK from the host the ready flag in the {{< regref "configin" >}} register will be
cleared and the bit corresponding to the endpoint number will be set
in the {{< regref "in_sent" >}} register which will cause a pkt_sent
interrupt. Software can return the buffer to the free pool and write a
1 to clear the bit in the {{< regref "in_sent" >}} register. Note that streaming can be
achieved if the next buffer has been prepared and is written to the
{{< regref "configin" >}} register when the interrupt is received.

A Control transfer may need an IN data transfer. Therefore when a
SETUP transaction is received for an endpoint the ready bit is cleared
in {{< regref "configin" >}} to cancel any buffer that was pending being sent to the
host from the Endpoint. When this is done the pending bit will be
set. The transfer must be queued again after the Control transfer is
completed.

A link level reset will also cancel pending IN transactions by
clearing the ready bit and setting the pending bit.

In general the 32 buffers will be allocated with one being processed
following reception, 4 in the available-buffer FIFO and 12 (worst
case) waiting transmission in the {{< regref "configin" >}} registers. This leaves 15
for preparation of next transmission (which would need 12 in the worst
case of one per endpoint) and the free pool.


# Design Details


# Programmers Guide


## Initialization

The basic hardware initialization is to (in any order) fill the
Available buffer FIFO, enable reception of SETUP and OUT packets on
Endpoint 0 (this is the control endpoint that the host will use to
configure the interface), enable reception of SETUP and OUT packets on
any endpoints that accept them and enable any required
interrupts. Finally the interface is enabled by setting the
{{< regref "usbctrl.enable" >}} bit. Setting this bit will cause the USB device to
assert the Full-Speed pullup on the D+ line, which is used by the host
to detect the device. In most cases there is no need to configure the
device ID ({{< regref "usbctrl.device_address" >}}) at this point -- the line will be
in reset and the hardware will have forced the device ID to zero.

The second stage of initialization is done under control of the host,
which will use control transfers (always beginning with SETUP
transactions) to Endpoint 0. Initially these will be sent to device
ID 0. When a Set Address request is received the device ID received
must be stored in the {{< regref "usbctrl.device_address" >}} register. Note that
device 0 is used for the entire control transaction setting the new
device ID, so writing the new ID to the register should not be done
until the ACK for the Status stage (see USB specification) has been
received.


## Buffers

The driver needs to manage the buffers in the interface SRAM. Each
buffer can hold the maximum length packet (64 bytes). Other than for
data movement this is most likely done based on their buffer
identifier which is a small integer between zero and (SRAM
size-in-bytes)/(MaxPacket-in-bytes).

In order to avoid unintentionally stalling the interface there must be
buffers available when the host sends data to the device (an OUT or
STATUS transaction). The driver needs to ensure (1) there are always
buffer identifiers in the Available buffer FIFO (2) the receive FIFO
is not full. If the AV FIFO is empty or the RX FIFO is full when data
is received a NAK will be returned to the host, requesting the packet
be retried later. Generating NAK with this mechanism is generally to
be avoided (for example the host expects a device will always accept
STATUS packets to endpoint 0).

Keeping the AV FIFO full can be done with a simple loop, adding
buffers from the software managed free-pool until the FIFO is full. A
simpler policy of just adding a buffer to the AV FIFO everytime one is
removed from the RX FIFO should work on average, but will be slightly
worse when a burst of packets are received.

Flow control (using NAKs) may be done per-endpoint using the
{{< regref "rxenable" >}} register. If this does not indicate OUT packet reception
is enabled then any packet will receive a NAK to request a retry
later. This should only be done for short durations or the host may
timeout the transaction.


## Reception

The host will send OUT or SETUP transactions when it wants to transfer
data to the device. The data packets are directed to a particular
endpoint, and the maximum packet size is set per-endpoint in its
Endpoint Descriptor (this must be the same or smaller than the maximum
packet size supported by the device). A received interrupt is raised
whenever there is one or more packets in the RX FIFO. The driver
should pop the information from the FIFO by reading the {{< regref "rxfifo" >}}
register, which gives (a) the buffer ID that the data was received in
(b) the data length, in bytes, received (c) the endpoint to which the
packet was sent (d) an indication if the packet was sent with an OUT
or STATUS transaction. Note that the data length could be between 0
and the maximum packet size -- in some situations a zero length packet
is used as an acknowledgement or end of transmission.

The data length does not include the packet CRC. (The CRC bytes are
written to the buffer if they fit within the maximum buffer size.)
Packets with a bad CRC will **not** be transferred to the RX FIFO, the
hardware will request a retry.


## Transmission

Data is transferred to the host based on the host requesting a
transfer with an IN transaction. The host will only generate IN
requests if the endpoint is declared as an IN endpoint in its Endpoint
Descriptor (note that two descriptors are needed if the same endpoint
is used for both IN and OUT transfers). The Endpoint Descriptor also
includes a description of the frequency the endpoint should be polled.

Data is queued for transmission by writing the corresponding
{{< regref "configin" >}} register with the buffer ID containing the data, the
length in bytes of data (0 to maximum packet length) and setting the
Rdy bit. This data (with the packet CRC) will be sent as a response to
the next IN transaction on the endpoint. When the host ACKs the data
the Rdy bit is cleared, the bit corresponding to the endpoint is set
in the {{< regref "in_sent" >}} register and a transmit interrupt is raised. If the
host does not ACK the data then the packet will be retried. When the
packet transmission has been noted by the driver the endpoint bit
should be cleared by writing a 1 to it in the {{< regref "in_sent" >}} register.

Note that the {{< regref "configin" >}} for an endpoint is a single register, so no
new data packet should be queued until the previous packet has been
acknowledged. This causes a problem if a Control Transaction is
received on an endpoint with a transmission pending because the
Control Transaction may require an IN packet. Therefore the hardware
will **clear the rdy bit** if an enabled SETUP transaction is received
on any endpoint and **set the pending bit** if there was data
pending. The driver must remember the pending transfer and, after the
Control transaction is complete, write it back to the {{< regref "configin" >}}
register with the rdy bit set.


## Stall

The {{< regref "stall" >}} register is used to Stall an endpoint. 
This is used if it is shutdown for some reason, or to signal certain error conditions (functional stall). 
Control endpoints also use a STALL to indicate unsupported requests (protocol stall). 
This register is used in both cases. Unused endpoints can have their {{< regref "stall" >}} register bit left clear, so in many cases there is no need to use the {{< regref "stall" >}} register. 
If the stall bit is set for an endpoint then the STALL response will be provided to all IN or OUT requests on that endpoint.

In the case of a protocol stall, the device must send a STALL for all IN and OUT requests until the next SETUP token is received. 
To support this, the software sets the STALL bit for an endpoint when an unsupported transfer is requested. 
The hardware will then send a STALL response to all IN/OUT transactions until the next SETUP is received for this endpoint.
Receiving the **SETUP token then clears the STALL flag** for the endpoint. 
The hardware then sends NAKs to any IN/OUT requets until the software has decided what action to take for the new SETUP request.


## Register Table

{{< registers "hw/ip/usbdev/data/usbdev.hjson" >}}
