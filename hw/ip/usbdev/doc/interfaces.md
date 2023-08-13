# Hardware Interfaces

<!-- BEGIN CMDGEN util/regtool.py --interfaces ./hw/ip/usbdev/data/usbdev.hjson -->
Referring to the [Comportable guideline for peripheral device functionality](https://opentitan.org/book/doc/contributing/hw/comportability), the module **`usbdev`** has the following hardware interfaces defined
- Primary Clock: **`clk_i`**
- Other Clocks: **`clk_aon_i`**
- Bus Device Interfaces (TL-UL): **`tl`**
- Bus Host Interfaces (TL-UL): *none*

## Peripheral Pins for Chip IO

| Pin name   | Direction   | Description         |
|:-----------|:------------|:--------------------|
| sense      | input       | USB host VBUS sense |
| usb_dp     | inout       | USB data D+         |
| usb_dn     | inout       | USB data D-         |

## [Inter-Module Signals](https://opentitan.org/book/doc/contributing/hw/comportability/index.html#inter-signal-handling)

| Port Name                  | Package::Struct             | Type    | Act   |   Width | Description                                                                                        |
|:---------------------------|:----------------------------|:--------|:------|--------:|:---------------------------------------------------------------------------------------------------|
| usb_rx_d                   | logic                       | uni     | rcv   |       1 | USB RX data from an external differential receiver, if available                                   |
| usb_tx_d                   | logic                       | uni     | req   |       1 | USB transmit data value (not used if usb_tx_se0 is set)                                            |
| usb_tx_se0                 | logic                       | uni     | req   |       1 | Force transmission of a USB single-ended zero (i.e. both D+ and D- are low) regardless of usb_tx_d |
| usb_tx_use_d_se0           | logic                       | uni     | req   |       1 | Use the usb_tx_d and usb_tx_se0 TX interface, instead of usb_dp_o and usb_dn_o                     |
| usb_dp_pullup              | logic                       | uni     | req   |       1 | USB D+ pullup control                                                                              |
| usb_dn_pullup              | logic                       | uni     | req   |       1 | USB D- pullup control                                                                              |
| usb_rx_enable              | logic                       | uni     | req   |       1 | USB differential receiver enable                                                                   |
| usb_ref_val                | logic                       | uni     | req   |       1 |                                                                                                    |
| usb_ref_pulse              | logic                       | uni     | req   |       1 |                                                                                                    |
| usb_aon_suspend_req        | logic                       | uni     | req   |       1 |                                                                                                    |
| usb_aon_wake_ack           | logic                       | uni     | req   |       1 |                                                                                                    |
| usb_aon_bus_reset          | logic                       | uni     | rcv   |       1 |                                                                                                    |
| usb_aon_sense_lost         | logic                       | uni     | rcv   |       1 |                                                                                                    |
| usb_aon_wake_detect_active | logic                       | uni     | rcv   |       1 |                                                                                                    |
| ram_cfg                    | prim_ram_2p_pkg::ram_2p_cfg | uni     | rcv   |       1 |                                                                                                    |
| tl                         | tlul_pkg::tl                | req_rsp | rsp   |       1 |                                                                                                    |

## Interrupts

| Interrupt Name   | Type   | Description                                                                                                                                                                                                                                                                                          |
|:-----------------|:-------|:-----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------|
| pkt_received     | Event  | Raised if a packet was received using an OUT or SETUP transaction. This interrupt is directly tied to whether the RX FIFO is empty, so it should be cleared only after handling the FIFO entry.                                                                                                      |
| pkt_sent         | Event  | Raised if a packet was sent as part of an IN transaction. This interrupt is directly tied to whether a sent packet has not been acknowledged in the [`in_sent`](registers.md#in_sent) register. It should be cleared only after clearing all bits in the [`in_sent`](registers.md#in_sent) register. |
| disconnected     | Event  | Raised if VBUS is lost thus the link is disconnected.                                                                                                                                                                                                                                                |
| host_lost        | Event  | Raised if link is active but SOF was not received from host for 4.096 ms. The SOF should be every 1 ms.                                                                                                                                                                                              |
| link_reset       | Event  | Raised if the link is at SE0 longer than 3 us indicating a link reset (host asserts for min 10 ms, device can react after 2.5 us).                                                                                                                                                                   |
| link_suspend     | Event  | Raised if the line has signaled J for longer than 3ms and is therefore in suspend state.                                                                                                                                                                                                             |
| link_resume      | Event  | Raised when the link becomes active again after being suspended.                                                                                                                                                                                                                                     |
| av_empty         | Event  | Raised when the AV FIFO is empty and the device interface is enabled. This interrupt is directly tied to the FIFO status, so the AV FIFO must be provided a free buffer before the interrupt is cleared. If the condition is not cleared, the interrupt can re-assert.                               |
| rx_full          | Event  | Raised when the RX FIFO is full and the device interface is enabled. This interrupt is directly tied to the FIFO status, so the RX FIFO must have an entry removed before the interrupt is cleared. If the condition is not cleared, the interrupt can re-assert.                                    |
| av_overflow      | Event  | Raised if a write was done to the Available Buffer FIFO when the FIFO was full.                                                                                                                                                                                                                      |
| link_in_err      | Event  | Raised if a packet to an IN endpoint started to be received but was then dropped due to an error. After transmitting the IN payload, the USB device expects a valid ACK handshake packet. This error is raised if either the packet or CRC is invalid or a different token was received.             |
| rx_crc_err       | Event  | Raised if a CRC error occured.                                                                                                                                                                                                                                                                       |
| rx_pid_err       | Event  | Raised if an invalid packed identifier (PID) was received.                                                                                                                                                                                                                                           |
| rx_bitstuff_err  | Event  | Raised if an invalid bitstuffing was received.                                                                                                                                                                                                                                                       |
| frame            | Event  | Raised when the USB frame number is updated with a valid SOF.                                                                                                                                                                                                                                        |
| powered          | Event  | Raised if VBUS is applied.                                                                                                                                                                                                                                                                           |
| link_out_err     | Event  | Raised if a packet to an OUT endpoint started to be received but was then dropped due to an error. This error is raised if the data toggle, token, packet and/or CRC are invalid, if the Available Buffer FIFO is empty or if the Received Buffer FIFO is full.                                      |

## Security Alerts

| Alert Name   | Description                                                                       |
|:-------------|:----------------------------------------------------------------------------------|
| fatal_fault  | This fatal alert is triggered when a fatal TL-UL bus integrity fault is detected. |

## Security Countermeasures

| Countermeasure ID    | Description                      |
|:---------------------|:---------------------------------|
| USBDEV.BUS.INTEGRITY | End-to-end bus integrity scheme. |


<!-- END CMDGEN -->
