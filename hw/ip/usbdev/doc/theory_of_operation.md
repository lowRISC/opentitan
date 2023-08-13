# Theory of Operation

A useful quick reference for USB Full-Speed is [USB Made Simple, Part 3 - Data Flow.](https://www.usbmadesimple.co.uk/ums_3.htm)

The block diagram shows a high level view of the USB device including the main register access paths.

![Block Diagram](../doc/usbdev_block.svg)


## Clocking

The USB Full-Speed interface runs at a data rate of 12 MHz.
The interface runs at four times this frequency and must be clocked from an accurate 48 MHz clock source.
The USB specification for a Full-Speed device requires the average bit rate is 12 Mbps +/- 0.25%, so the clock needs to support maximum error of 2,500 ppm.
The maximum allowable integrated jitter is +/- 1 ns over 1 to 7 bit periods.

This module features the following output signals to provide a reference for synchronizing the 48 MHz clock source:
- `usb_ref_pulse_o` indicates the reception of a start of frame (SOF) packet.
  The host is required to send a SOF packet every 1 ms.
- `usb_ref_val_o` serves as a valid signal for `usb_ref_pulse_o`.
  It is set to one after the first SOF packet is received and remains high as long as `usb_ref_pulse_o` continues to behave as expected.
  As soon as it is detected that SOF will not be received as expected (usually because the link is no longer active), `usb_ref_val_o` deasserts to zero until after the next `usb_ref_pulse_o`.

Both these signals are synchronous to the 48 MHz clock.
They can be forced to zero by setting [`phy_config.usb_ref_disable`](registers.md#phy_config) to `1`.

To successfully receive SOF packets without errors and thereby enabling clock synchronization, the initial accuracy of the 48 MHz clock source should be within 3.2% or 32,000 ppm.
This requirement comes from the fact that the SOF packet has a length of 24 bits (plus 8-bit sync field).
The first 8 bits are used to transfer the SOF packet ID (8'b01011010).
Internally, the USB device dynamically adjusts the sampling point based on observed line transitions.
Assuming the last bit of the SOF packet ID is sampled in the middle of the eye, the drift over the remaining 16 bits of the packet must be lower than half a bit (10^6 * (0.5/16) = 32,000 ppm).

To externally monitor the 48 MHz clock, the USB device supports an oscillator test mode which can be enabled by setting [`phy_config.tx_osc_test_mode`](registers.md#phy_config) to `1`.
In this mode, the device constantly transmits a J/K pattern but no longer receives SOF packets.
Consequently, it does not generate reference pulses for clock synchronization.
The clock might drift off.

Control transfers pass through synchronous FIFOs or have a ready bit synchronized across the clock domain boundary.
A dual-port synchronous buffer SRAM is used for data transfers, and the bus clock and USB clock come from the same 48 MHz input.
The wake detection module is clocked by a separate clock, and a couple registers are used to interface with it.
Any bus-related clock domain crossings must happen outside the core, except for the transition between the 48 MHz clock and the wake detection module's clock.
The 48 MHz clock must be enabled to reach the registers in `usbdev`.


## USB Interface Pins

Full-Speed USB uses a bidirectional serial interface as shown in Figure 7-24 of the [USB 2.0 Full-Speed specification](https://www.usb.org/document-library/usb-20-specification).
For reasons of flexibility, this IP block features multiple transmit and receive paths for interfacing with various transceivers.

The following sections describe how the various input/output signals relate to the USB interface pins for the different receive and transmit configurations.


### Data Transmit

The IP block supports two different encodings, driving out on separate TX interfaces.
The default encoding looks like the USB bus, with D+ and D- values driven on usb_dp_o and usb_dn_o pins.
The alternate encoding uses usb_se0_o to indicate a single-ended zero (SE0), and usb_d_o encodes K/J (when usb_se0_o is low).
The TX mode can be selected by setting the `use_tx_d_se0` bit in [`phy_config`](registers.md#phy_config) to either 1 (alternate, using d/se0) or 0 (default, using dp/dn).

The following table summarizes how the different output signals relate to the USB interface pins.

|  External Pins | Internal Signals | Notes |
|----------------|------------------|-------|
| D+, D-         | dp_o, dn_o       | Data output with an encoding like the USB bus, intended to go directly to pads for supported targets. On an FPGA, the components should be used with a USB transceiver, as the regular bidirectional I/O cells will likely not be USB compliant. |
| [Alt TX Data]  | se0_o            | Signal Single-Ended Zero (SE0) link state to a USB transceiver. |
| [Alt TX Data]  | d_o              | Data output used for encoding K and J, for interfacing with a USB transceiver. |
|   [TX Mode]    | tx_use_d_se0_o   | Indicates the selected TX interface: use dp_o and dn_o (0) or use d_o and se0_o (1). |

Note that according to the [Comportable guideline for peripheral functionality](../../../../doc/contributing/hw/comportability/README.md), every output signal `name_o` has a dedicated output enable `name_en_o`.
For TX data, these separate signals `dp_en_o` and `dn_en_o` all correspond to the same TX or output enable signal (`OE` in the USB spec).
The other signals listed are of the "intersignal" variety, and they do not go directly to pads or have dedicated output enable signals.


### Data Receive

The IP block supports recovery of the differential K and J symbols from the output of an external differential receiver or directly from the D+/D- pair.
The RX mode can be selected to use a differential receiver's output by setting the `use_diff_rcvr` bit in [`phy_config`](registers.md#phy_config).
The D+/D- pair is always used to detect the single-ended zero (SE0) state.

The following table summarizes how the different input signals relate to the USB interface pins.

|  External Pins | Internal Signals | Notes |
|----------------|------------------|-------|
| D+, D-         | dp_i, dn_i       | D+ and D- signals passing into the IP single-ended, intended to go directly to pads for supported targets. These signals are used to detect the SE0 link state, and if a differential receiver is not present, they are also used for K and J symbols. On an FPGA, the components should be used with a USB transceiver, as the bidirectional regular IO cells will likely not be USB compliant. |
| [Diff Rcvr Out]| d_i              | Data input for interfacing with a differential receiver, which is required for this input. |


### Non-Data Pins

The USB device features the following non-data pins.

|  External Pins | Internal Signals         | Notes |
|----------------|--------------------------|-------|
| sense (VBUS)   | sense_i                  | The sense pin indicates the presence of VBUS from the USB host. |
| [pullup]       | dp_pullup_o, dn_pullup_o | When dp_pullup_o or dn_pullup_o asserts a 1.5k pullup resistor should be connected to D+ or D-, respectively. This can be done inside the chip or with an external pin. A permanently connected resistor could be used if the pin flip feature is not needed, but this is not recommended because there is then no way to force the device to appear to unplug. Only one of the pullup signals can be asserted at any time. The selection is based on the `pinflip` bit in [`phy_config`](registers.md#phy_config). Because this is a Full-Speed device the resistor must be on the D+ pin, so when `pinflip` is zero, dp_pullup_o is used. |
| [suspend]      | suspend_o                | The suspend pin indicates to the USB transceiver that a constant idle has been detected on the link and the device is in the Suspend state (see Section 7.1.7.6 of the [USB 2.0 specification](https://www.usb.org/document-library/usb-20-specification)). |
| [rx_enable]    | rx_enable_o              | The rx_enable pin turns on/off a differential receiver. It is enabled via a CSR and automatically disabled when the device suspends. |

The USB host will identify itself to the device by enabling the 5V VBUS power.
It may do a hard reset of a port by removing and reasserting VBUS (the Linux driver will do this when it finds a port in an inconsistent state or a port that generates errors during enumeration).
The IP block detects VBUS through the sense pin.
This pin is always an input and should be externally connected to detect the state of the VBUS.
Note that this may require a resistor divider or (for USB-C where VBUS can be up to 20V) active level translation to an acceptable voltage for the input pin.

A Full-Speed device identifies itself by providing a 1.5k pullup resistor (to 3.3V) on the D+ line.
The IP block produces a signal `dp_pullup_o` that is asserted when this resistor should be presented.
This signal will be asserted whenever the interface is enabled and VBUS is present.
In an FPGA implementation, this signal can drive a 3.3V output pin that is driven high when the signal is asserted and set high impedance when the signal is deasserted, and the output pin used to drive a 1.5k resistor connected on the board to the D+ line.
Alternatively, it can be used to enable an internal 1.5k pullup on the D+ pin.

This USB device supports the flipping of D+/D-.
If the `pinflip` bit in [`phy_config`](registers.md#phy_config) is set, the data pins are flipped internally, meaning the 1.5k pullup resistor needs to be on the external D- line.
To control the pullup on the D- line, this USB device features `dn_pullup_o` signal.
Of the two pullup signals `dp_pullup_o` and `dn_pullup_o`, only one can be enabled at any time.
As this is a Full-Speed device, `dp_pullup_o`, i.e., the pullup on D+ is used by default (`pinflip` equals zero).

## USB Link State

The USB link has a number of states.
These are detected and reported in [`usbstat.link_state`](registers.md#usbstat) and state changes are reported using interrupts.
The FSM implements a subset of the USB device state diagram shown in Figure 9-1 of the [USB 2.0 specification.](https://www.usb.org/document-library/usb-20-specification)

|State| Description |
|-----|-------------|
|Disconnected | The link is disconnected. This is signaled when the VBUS is not driven by the host, which results in the sense input pin being low, or when the user has not connected the pull-up by enabling the interface. An interrupt is raised on entering this state.|
|Powered| The device has been powered as VBUS is being driven by the host and the user has connected the pull-up, but the device has not been reset yet. The link is reset whenever the D+ and D- are both low (an SE0 condition) for an extended period. The host will assert reset for a minimum of 10 ms, but the USB specification allows the device to detect and respond to a reset after 2.5 us. The implementation here will report the reset state and raise an interrupt when the link is in SE0 for 3 us.|
|Powered Suspended| The link is suspended when at idle (a J condition) for more than 3 ms. An interrupt is generated when the suspend is detected and a resume interrupt is generated when the link exits the suspend state. This state is entered, if the device has not been reset yet.|
|Active No SOF| The link has been reset and can begin receiving packets, but no Start-of-Frame packets have yet been seen.|
|Active| The link is active when it is running normally. |
|Suspended| Similar to 'Powered Suspended', but the device was in the active state before being suspended.|
|Resuming| The link is awaiting the end of resume signaling before transitioning to the Active No SOF state.|

|Link Events| Description |
|-----------|-------------|
|Disconnect| VBUS has been lost. |
|Link Reset| The link has been in the SE0 state for 3 us.|
|Link Suspend| The link has been in the J state for more than 3 ms, upon which we have to enter the Suspend state.|
|Link Resume| The link has been driven to a non-J state after being in Suspend. For the case of resuming to active link states, the end of resume signaling has occurred.|
|Host Lost| Signaled using an interrupt if the link is active but a start of frame (SOF) packet has not been received from the host in 4 frames. The host is required to send a SOF packet every 1 ms. This is not an expected condition.|


## USB Protocol Engine

The USB 2.0 Full-Speed Protocol Engine is provided by the common USB interface code and is, strictly speaking, not part of this USB device module.

At the lowest level of the USB stack the transmit bitstream is serialized, converted to non-return-to-zero inverted (NRZI) encoding with bit-stuffing and sent to the transmitter.
The received bitstream is recovered, clock aligned and decoded and has bit-stuffing removed.
The recovered clock alignment is used for transmission.

The higher level protocol engine forms the bitstream into packets, performs CRC checking and recognizes IN, OUT and SETUP transactions.
These are presented to this module without buffering.
This means the USB device module must accept or provide data when requested.
The protocol engine may cancel a transaction because of a bad cyclic redundancy check (CRC) or request a retry if an acknowledgment (ACK) was not received.


## Buffer Interface

A 2 kB SRAM is used as a packet buffer to hold data between the system and the USB interface.
This is divided up into 32 buffers each containing 64 bytes.
This is an asynchronous dual-port SRAM with software accessing from the bus clock domain and the USB interface accessing from the USB 48 MHz clock domain.


### Reception

Software provides buffers for packet reception through a 4-entry Available Buffer FIFO.
(More study needed but four seems about right: one just returned to software, one being filled, one ready to be filled, and one for luck.)
The [`rxenable_out`](registers.md#rxenable_out) and [`rxenable_setup`](registers.md#rxenable_setup) registers is used to indicate which endpoints will accept data from the host using OUT or SETUP transactions, respectively.
When a packet is transferred from the host to the device (using an OUT or SETUP transaction) and reception of that type of transaction is enabled for the requested endpoint, the next buffer ID is pulled from the Available Buffer FIFO.
The packet data is written to the corresponding buffer in the packet buffer (the 2 kB SRAM).
If the packet is correctly received, an ACK is returned to the host.
In addition, the buffer ID, the packet size, an out/setup flag and the endpoint ID are passed back to software using the Received Buffer FIFO and a pkt_received interrupt is raised.

Software should immediately provide a free buffer for future reception by writing the corresponding buffer ID to the Available Buffer FIFO.
It can then process the packet and eventually return the received buffer to the free pool.
This allows streaming on a single endpoint or across a number of endpoints.
If the packets cannot be consumed at the rate they are received, software can implement selective flow control by clearing [`rxenable_out`](registers.md#rxenable_out) for a particular endpoint, which will result in a request to that endpoint being NAKed (negative acknowledgment).
In the unfortunate event that the Available Buffer FIFO is empty or the Received Buffer FIFO is full, all OUT transactions are NAKed and SETUP transactions are ignored.
In that event, the host will retry the transaction (up to some maximum attempts or time).

There are two options for a given OUT endpoint's flow control, controlled by the [`set_nak_out`](registers.md#set_nak_out) register.
If `set_nak_out` is 0 for the endpoint, it will accept packets as long as there are buffers available in the Available Buffer FIFO and space available in the Received Buffer FIFO.
For timing, this option implies that software may not be able to affect the response to a given transaction, and buffer availability is the only needed factor.
If `set_nak_out` is 1 for the endpoint, it will clear its corresponding bit in the [`rxenable_out`](registers.md#rxenable_out) register, forcing NAK responses to OUT transactions to that endpoint until software can intervene.
That option uses NAK to defer the host, and this enables software to implement features that require protocol-level control at transaction boundaries, such as when implementing the functional stall.


### Transmission

To send data to the host in response to an IN transaction, software first writes the data into a free buffer.
Then, it writes the buffer ID, data length and rdy flag to the [`configin`](registers.md#configin) register of the corresponding endpoint.
When the host next does an IN transaction to that endpoint, the data will be sent from the buffer.
On receipt of the ACK from the host, the rdy bit in the [`configin`](registers.md#configin) register will be cleared, and the bit corresponding to the endpoint ID will be set in the [`in_sent`](registers.md#in_sent) register causing a pkt_sent interrupt to be raised.
Software can return the buffer to the free pool and write a 1 to clear the endpoint bit in the [`in_sent`](registers.md#in_sent) register.
Note that streaming can be achieved if the next buffer has been prepared and is written to the [`configin`](registers.md#configin) register when the interrupt is received.

A Control transfer requires one or more IN transactions, either during the data stage or the status stage.
Therefore, when a SETUP transaction is received for an endpoint, any buffers that are waiting to be sent out to the host from that endpoint are canceled by clearing the rdy bit in the corresponding [`configin`](registers.md#configin) register.
To keep track of such canceled buffers, the pend bit in the same register is set.
The transfer must be queued again after the Control transfer is completed.

Similarly, a Link Reset cancels any waiting IN transactions by clearing the rdy bit in the [`configin`](registers.md#configin) register of all endpoints.
The pend bit in the [`configin`](registers.md#configin) register is set for all endpoints with a pending IN transaction.


### Buffer Count and Size

Under high load, the 32 buffers of the packet buffer (2 kB SRAM) are allocated as follows:
- 1 is being processed following reception,
- 4 are in the Available Buffer FIFO, and
- 12 (worst case) waiting transmissions in the [`configin`](registers.md#configin) registers.
This leaves 15 buffers for preparation of future transmissions (which would need 12 in the worst case of one per endpoint) and the free pool.

The size of 64 bytes per buffer satisfies the maximum USB packet size for a Full-Speed interface for Control transfers (max may be 8, 16, 32 or 64 bytes), Bulk Transfers (max is 64 bytes) and Interrupt transfers (max is 64 bytes).
It is small for Isochronous transfers (which have a max size of 1023 bytes).
The interface will need extending for high rate isochronous use (a possible option would be to allow up to 8 or 16 64-byte buffers to be aggregated as the isochronous buffer).


# Design Details
