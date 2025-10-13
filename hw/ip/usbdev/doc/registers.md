# Registers

<!-- BEGIN CMDGEN util/regtool.py -d ./hw/ip/usbdev/data/usbdev.hjson -->
## Summary

| Name                                         | Offset   |   Length | Description                                                                |
|:---------------------------------------------|:---------|---------:|:---------------------------------------------------------------------------|
| usbdev.[`INTR_STATE`](#intr_state)           | 0x0      |        4 | Interrupt State Register                                                   |
| usbdev.[`INTR_ENABLE`](#intr_enable)         | 0x4      |        4 | Interrupt Enable Register                                                  |
| usbdev.[`INTR_TEST`](#intr_test)             | 0x8      |        4 | Interrupt Test Register                                                    |
| usbdev.[`ALERT_TEST`](#alert_test)           | 0xc      |        4 | Alert Test Register                                                        |
| usbdev.[`usbctrl`](#usbctrl)                 | 0x10     |        4 | USB Control                                                                |
| usbdev.[`ep_out_enable`](#ep_out_enable)     | 0x14     |        4 | Enable an endpoint to respond to transactions in the downstream direction. |
| usbdev.[`ep_in_enable`](#ep_in_enable)       | 0x18     |        4 | Enable an endpoint to respond to transactions in the upstream direction.   |
| usbdev.[`usbstat`](#usbstat)                 | 0x1c     |        4 | USB Status                                                                 |
| usbdev.[`avoutbuffer`](#avoutbuffer)         | 0x20     |        4 | Available OUT Buffer FIFO                                                  |
| usbdev.[`avsetupbuffer`](#avsetupbuffer)     | 0x24     |        4 | Available SETUP Buffer FIFO                                                |
| usbdev.[`rxfifo`](#rxfifo)                   | 0x28     |        4 | Received Buffer FIFO                                                       |
| usbdev.[`rxenable_setup`](#rxenable_setup)   | 0x2c     |        4 | Receive SETUP transaction enable                                           |
| usbdev.[`rxenable_out`](#rxenable_out)       | 0x30     |        4 | Receive OUT transaction enable                                             |
| usbdev.[`set_nak_out`](#set_nak_out)         | 0x34     |        4 | Set NAK after OUT transactions                                             |
| usbdev.[`in_sent`](#in_sent)                 | 0x38     |        4 | IN Transaction Sent                                                        |
| usbdev.[`out_stall`](#out_stall)             | 0x3c     |        4 | OUT Endpoint STALL control                                                 |
| usbdev.[`in_stall`](#in_stall)               | 0x40     |        4 | IN Endpoint STALL control                                                  |
| usbdev.[`configin_0`](#configin)             | 0x44     |        4 | Configure IN Transaction                                                   |
| usbdev.[`configin_1`](#configin)             | 0x48     |        4 | Configure IN Transaction                                                   |
| usbdev.[`configin_2`](#configin)             | 0x4c     |        4 | Configure IN Transaction                                                   |
| usbdev.[`configin_3`](#configin)             | 0x50     |        4 | Configure IN Transaction                                                   |
| usbdev.[`configin_4`](#configin)             | 0x54     |        4 | Configure IN Transaction                                                   |
| usbdev.[`configin_5`](#configin)             | 0x58     |        4 | Configure IN Transaction                                                   |
| usbdev.[`configin_6`](#configin)             | 0x5c     |        4 | Configure IN Transaction                                                   |
| usbdev.[`configin_7`](#configin)             | 0x60     |        4 | Configure IN Transaction                                                   |
| usbdev.[`configin_8`](#configin)             | 0x64     |        4 | Configure IN Transaction                                                   |
| usbdev.[`configin_9`](#configin)             | 0x68     |        4 | Configure IN Transaction                                                   |
| usbdev.[`configin_10`](#configin)            | 0x6c     |        4 | Configure IN Transaction                                                   |
| usbdev.[`configin_11`](#configin)            | 0x70     |        4 | Configure IN Transaction                                                   |
| usbdev.[`out_iso`](#out_iso)                 | 0x74     |        4 | OUT Endpoint isochronous setting                                           |
| usbdev.[`in_iso`](#in_iso)                   | 0x78     |        4 | IN Endpoint isochronous setting                                            |
| usbdev.[`out_data_toggle`](#out_data_toggle) | 0x7c     |        4 | OUT Endpoints Data Toggles                                                 |
| usbdev.[`in_data_toggle`](#in_data_toggle)   | 0x80     |        4 | IN Endpoints Data Toggles                                                  |
| usbdev.[`phy_pins_sense`](#phy_pins_sense)   | 0x84     |        4 | USB PHY pins sense.                                                        |
| usbdev.[`phy_pins_drive`](#phy_pins_drive)   | 0x88     |        4 | USB PHY pins drive.                                                        |
| usbdev.[`phy_config`](#phy_config)           | 0x8c     |        4 | USB PHY Configuration                                                      |
| usbdev.[`wake_control`](#wake_control)       | 0x90     |        4 | USB wake module control for suspend / resume                               |
| usbdev.[`wake_events`](#wake_events)         | 0x94     |        4 | USB wake module events and debug                                           |
| usbdev.[`fifo_ctrl`](#fifo_ctrl)             | 0x98     |        4 | FIFO control register                                                      |
| usbdev.[`count_out`](#count_out)             | 0x9c     |        4 | Counter for OUT side USB events.                                           |
| usbdev.[`count_in`](#count_in)               | 0xa0     |        4 | Counter for IN side USB events.                                            |
| usbdev.[`count_nodata_in`](#count_nodata_in) | 0xa4     |        4 | Count of IN transactions for which no packet data was available.           |
| usbdev.[`count_errors`](#count_errors)       | 0xa8     |        4 | Count of error conditions detected on token packets from the host.         |
| usbdev.[`buffer`](#buffer)                   | 0x800    |     2048 | 2 KiB packet buffer. Divided into thirty two 64-byte buffers.              |

## INTR_STATE
Interrupt State Register
- Offset: `0x0`
- Reset default: `0x0`
- Reset mask: `0x3ffff`

### Fields

```wavejson
{"reg": [{"name": "pkt_received", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "pkt_sent", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "disconnected", "bits": 1, "attr": ["rw1c"], "rotate": -90}, {"name": "host_lost", "bits": 1, "attr": ["rw1c"], "rotate": -90}, {"name": "link_reset", "bits": 1, "attr": ["rw1c"], "rotate": -90}, {"name": "link_suspend", "bits": 1, "attr": ["rw1c"], "rotate": -90}, {"name": "link_resume", "bits": 1, "attr": ["rw1c"], "rotate": -90}, {"name": "av_out_empty", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "rx_full", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "av_overflow", "bits": 1, "attr": ["rw1c"], "rotate": -90}, {"name": "link_in_err", "bits": 1, "attr": ["rw1c"], "rotate": -90}, {"name": "rx_crc_err", "bits": 1, "attr": ["rw1c"], "rotate": -90}, {"name": "rx_pid_err", "bits": 1, "attr": ["rw1c"], "rotate": -90}, {"name": "rx_bitstuff_err", "bits": 1, "attr": ["rw1c"], "rotate": -90}, {"name": "frame", "bits": 1, "attr": ["rw1c"], "rotate": -90}, {"name": "powered", "bits": 1, "attr": ["rw1c"], "rotate": -90}, {"name": "link_out_err", "bits": 1, "attr": ["rw1c"], "rotate": -90}, {"name": "av_setup_empty", "bits": 1, "attr": ["ro"], "rotate": -90}, {"bits": 14}], "config": {"lanes": 1, "fontsize": 10, "vspace": 170}}
```

|  Bits  |  Type  |  Reset  | Name                                            |
|:------:|:------:|:-------:|:------------------------------------------------|
| 31:18  |        |         | Reserved                                        |
|   17   |   ro   |   0x0   | [av_setup_empty](#intr_state--av_setup_empty)   |
|   16   |  rw1c  |   0x0   | [link_out_err](#intr_state--link_out_err)       |
|   15   |  rw1c  |   0x0   | [powered](#intr_state--powered)                 |
|   14   |  rw1c  |   0x0   | [frame](#intr_state--frame)                     |
|   13   |  rw1c  |   0x0   | [rx_bitstuff_err](#intr_state--rx_bitstuff_err) |
|   12   |  rw1c  |   0x0   | [rx_pid_err](#intr_state--rx_pid_err)           |
|   11   |  rw1c  |   0x0   | [rx_crc_err](#intr_state--rx_crc_err)           |
|   10   |  rw1c  |   0x0   | [link_in_err](#intr_state--link_in_err)         |
|   9    |  rw1c  |   0x0   | [av_overflow](#intr_state--av_overflow)         |
|   8    |   ro   |   0x0   | [rx_full](#intr_state--rx_full)                 |
|   7    |   ro   |   0x0   | [av_out_empty](#intr_state--av_out_empty)       |
|   6    |  rw1c  |   0x0   | [link_resume](#intr_state--link_resume)         |
|   5    |  rw1c  |   0x0   | [link_suspend](#intr_state--link_suspend)       |
|   4    |  rw1c  |   0x0   | [link_reset](#intr_state--link_reset)           |
|   3    |  rw1c  |   0x0   | [host_lost](#intr_state--host_lost)             |
|   2    |  rw1c  |   0x0   | [disconnected](#intr_state--disconnected)       |
|   1    |   ro   |   0x0   | [pkt_sent](#intr_state--pkt_sent)               |
|   0    |   ro   |   0x0   | [pkt_received](#intr_state--pkt_received)       |

### INTR_STATE . av_setup_empty
Raised when the Available SETUP Buffer FIFO is empty and the device interface is enabled.
This interrupt is directly tied to the FIFO status, so the Available SETUP Buffer FIFO must be provided with a free buffer before the interrupt can be cleared.

### INTR_STATE . link_out_err
Raised if a packet to an OUT endpoint started to be received but was then dropped due to an error.
This error is raised if the data toggle, token, packet and/or CRC are invalid, or if the appropriate Available OUT Buffer FIFO is empty and/or the Received Buffer FIFO is full when a packet should have been received.
Attempting to perform an OUT transaction to an endpoint that is stalled, i.e. its control bit in `out_stall` is set, will also cause this error to be raised.

### INTR_STATE . powered
Raised if VBUS is applied.

### INTR_STATE . frame
Raised when the USB frame number is updated with a valid SOF.

### INTR_STATE . rx_bitstuff_err
Raised if an invalid bitstuffing was received.

### INTR_STATE . rx_pid_err
Raised if an invalid Packet IDentifier (PID) was received.

### INTR_STATE . rx_crc_err
Raised if a CRC error occurred on a received packet.

### INTR_STATE . link_in_err
Raised if a packet to an IN endpoint started to be received but was
then dropped due to an error. After transmitting the IN payload,
the USB device expects a valid ACK handshake packet. This error is
raised if either the packet or CRC is invalid, leading to a NAK instead,
or if a different token was received.

### INTR_STATE . av_overflow
Raised if a write was done to either the Available OUT Buffer FIFO or the Available SETUP Buffer FIFO when the FIFO was full.

### INTR_STATE . rx_full
Raised when the RX FIFO is full and the device interface is enabled.
This interrupt is directly tied to the FIFO status, so the RX FIFO must have an entry removed before the interrupt is cleared.
If the condition is not cleared, the interrupt can re-assert.

### INTR_STATE . av_out_empty
Raised when the Available OUT Buffer FIFO is empty and the device interface is enabled.
This interrupt is directly tied to the FIFO status, so the Available OUT Buffer FIFO must be provided with a free buffer before the interrupt can be cleared.

### INTR_STATE . link_resume
Raised when the link becomes active again after being suspended.

### INTR_STATE . link_suspend
Raised if the line has signaled J for longer than 3ms and is therefore in suspend state.

### INTR_STATE . link_reset
Raised if the link is at SE0 longer than 3 us indicating a link reset (host asserts for min 10 ms, device can react after 2.5 us).

### INTR_STATE . host_lost
Raised if link is active but SOF was not received from host for 4.096 ms. The SOF should be every 1 ms.

### INTR_STATE . disconnected
Raised if VBUS is lost or the pullup is disabled, thus the link is disconnected.

### INTR_STATE . pkt_sent
Raised if a packet was sent as part of an IN transaction.
This interrupt is directly tied to whether a sent packet has not been acknowledged in the [`in_sent`](#in_sent) register.
It should be cleared only after clearing all bits in the [`in_sent`](#in_sent) register.

### INTR_STATE . pkt_received
Raised if a packet was received using an OUT or SETUP transaction.
This interrupt is directly tied to whether the RX FIFO is empty, so it should be cleared only after handling the FIFO entry.

## INTR_ENABLE
Interrupt Enable Register
- Offset: `0x4`
- Reset default: `0x0`
- Reset mask: `0x3ffff`

### Fields

```wavejson
{"reg": [{"name": "pkt_received", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "pkt_sent", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "disconnected", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "host_lost", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "link_reset", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "link_suspend", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "link_resume", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "av_out_empty", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "rx_full", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "av_overflow", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "link_in_err", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "rx_crc_err", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "rx_pid_err", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "rx_bitstuff_err", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "frame", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "powered", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "link_out_err", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "av_setup_empty", "bits": 1, "attr": ["rw"], "rotate": -90}, {"bits": 14}], "config": {"lanes": 1, "fontsize": 10, "vspace": 170}}
```

|  Bits  |  Type  |  Reset  | Name            | Description                                                               |
|:------:|:------:|:-------:|:----------------|:--------------------------------------------------------------------------|
| 31:18  |        |         |                 | Reserved                                                                  |
|   17   |   rw   |   0x0   | av_setup_empty  | Enable interrupt when [`INTR_STATE.av_setup_empty`](#intr_state) is set.  |
|   16   |   rw   |   0x0   | link_out_err    | Enable interrupt when [`INTR_STATE.link_out_err`](#intr_state) is set.    |
|   15   |   rw   |   0x0   | powered         | Enable interrupt when [`INTR_STATE.powered`](#intr_state) is set.         |
|   14   |   rw   |   0x0   | frame           | Enable interrupt when [`INTR_STATE.frame`](#intr_state) is set.           |
|   13   |   rw   |   0x0   | rx_bitstuff_err | Enable interrupt when [`INTR_STATE.rx_bitstuff_err`](#intr_state) is set. |
|   12   |   rw   |   0x0   | rx_pid_err      | Enable interrupt when [`INTR_STATE.rx_pid_err`](#intr_state) is set.      |
|   11   |   rw   |   0x0   | rx_crc_err      | Enable interrupt when [`INTR_STATE.rx_crc_err`](#intr_state) is set.      |
|   10   |   rw   |   0x0   | link_in_err     | Enable interrupt when [`INTR_STATE.link_in_err`](#intr_state) is set.     |
|   9    |   rw   |   0x0   | av_overflow     | Enable interrupt when [`INTR_STATE.av_overflow`](#intr_state) is set.     |
|   8    |   rw   |   0x0   | rx_full         | Enable interrupt when [`INTR_STATE.rx_full`](#intr_state) is set.         |
|   7    |   rw   |   0x0   | av_out_empty    | Enable interrupt when [`INTR_STATE.av_out_empty`](#intr_state) is set.    |
|   6    |   rw   |   0x0   | link_resume     | Enable interrupt when [`INTR_STATE.link_resume`](#intr_state) is set.     |
|   5    |   rw   |   0x0   | link_suspend    | Enable interrupt when [`INTR_STATE.link_suspend`](#intr_state) is set.    |
|   4    |   rw   |   0x0   | link_reset      | Enable interrupt when [`INTR_STATE.link_reset`](#intr_state) is set.      |
|   3    |   rw   |   0x0   | host_lost       | Enable interrupt when [`INTR_STATE.host_lost`](#intr_state) is set.       |
|   2    |   rw   |   0x0   | disconnected    | Enable interrupt when [`INTR_STATE.disconnected`](#intr_state) is set.    |
|   1    |   rw   |   0x0   | pkt_sent        | Enable interrupt when [`INTR_STATE.pkt_sent`](#intr_state) is set.        |
|   0    |   rw   |   0x0   | pkt_received    | Enable interrupt when [`INTR_STATE.pkt_received`](#intr_state) is set.    |

## INTR_TEST
Interrupt Test Register
- Offset: `0x8`
- Reset default: `0x0`
- Reset mask: `0x3ffff`

### Fields

```wavejson
{"reg": [{"name": "pkt_received", "bits": 1, "attr": ["wo"], "rotate": -90}, {"name": "pkt_sent", "bits": 1, "attr": ["wo"], "rotate": -90}, {"name": "disconnected", "bits": 1, "attr": ["wo"], "rotate": -90}, {"name": "host_lost", "bits": 1, "attr": ["wo"], "rotate": -90}, {"name": "link_reset", "bits": 1, "attr": ["wo"], "rotate": -90}, {"name": "link_suspend", "bits": 1, "attr": ["wo"], "rotate": -90}, {"name": "link_resume", "bits": 1, "attr": ["wo"], "rotate": -90}, {"name": "av_out_empty", "bits": 1, "attr": ["wo"], "rotate": -90}, {"name": "rx_full", "bits": 1, "attr": ["wo"], "rotate": -90}, {"name": "av_overflow", "bits": 1, "attr": ["wo"], "rotate": -90}, {"name": "link_in_err", "bits": 1, "attr": ["wo"], "rotate": -90}, {"name": "rx_crc_err", "bits": 1, "attr": ["wo"], "rotate": -90}, {"name": "rx_pid_err", "bits": 1, "attr": ["wo"], "rotate": -90}, {"name": "rx_bitstuff_err", "bits": 1, "attr": ["wo"], "rotate": -90}, {"name": "frame", "bits": 1, "attr": ["wo"], "rotate": -90}, {"name": "powered", "bits": 1, "attr": ["wo"], "rotate": -90}, {"name": "link_out_err", "bits": 1, "attr": ["wo"], "rotate": -90}, {"name": "av_setup_empty", "bits": 1, "attr": ["wo"], "rotate": -90}, {"bits": 14}], "config": {"lanes": 1, "fontsize": 10, "vspace": 170}}
```

|  Bits  |  Type  |  Reset  | Name            | Description                                                        |
|:------:|:------:|:-------:|:----------------|:-------------------------------------------------------------------|
| 31:18  |        |         |                 | Reserved                                                           |
|   17   |   wo   |   0x0   | av_setup_empty  | Write 1 to force [`INTR_STATE.av_setup_empty`](#intr_state) to 1.  |
|   16   |   wo   |   0x0   | link_out_err    | Write 1 to force [`INTR_STATE.link_out_err`](#intr_state) to 1.    |
|   15   |   wo   |   0x0   | powered         | Write 1 to force [`INTR_STATE.powered`](#intr_state) to 1.         |
|   14   |   wo   |   0x0   | frame           | Write 1 to force [`INTR_STATE.frame`](#intr_state) to 1.           |
|   13   |   wo   |   0x0   | rx_bitstuff_err | Write 1 to force [`INTR_STATE.rx_bitstuff_err`](#intr_state) to 1. |
|   12   |   wo   |   0x0   | rx_pid_err      | Write 1 to force [`INTR_STATE.rx_pid_err`](#intr_state) to 1.      |
|   11   |   wo   |   0x0   | rx_crc_err      | Write 1 to force [`INTR_STATE.rx_crc_err`](#intr_state) to 1.      |
|   10   |   wo   |   0x0   | link_in_err     | Write 1 to force [`INTR_STATE.link_in_err`](#intr_state) to 1.     |
|   9    |   wo   |   0x0   | av_overflow     | Write 1 to force [`INTR_STATE.av_overflow`](#intr_state) to 1.     |
|   8    |   wo   |   0x0   | rx_full         | Write 1 to force [`INTR_STATE.rx_full`](#intr_state) to 1.         |
|   7    |   wo   |   0x0   | av_out_empty    | Write 1 to force [`INTR_STATE.av_out_empty`](#intr_state) to 1.    |
|   6    |   wo   |   0x0   | link_resume     | Write 1 to force [`INTR_STATE.link_resume`](#intr_state) to 1.     |
|   5    |   wo   |   0x0   | link_suspend    | Write 1 to force [`INTR_STATE.link_suspend`](#intr_state) to 1.    |
|   4    |   wo   |   0x0   | link_reset      | Write 1 to force [`INTR_STATE.link_reset`](#intr_state) to 1.      |
|   3    |   wo   |   0x0   | host_lost       | Write 1 to force [`INTR_STATE.host_lost`](#intr_state) to 1.       |
|   2    |   wo   |   0x0   | disconnected    | Write 1 to force [`INTR_STATE.disconnected`](#intr_state) to 1.    |
|   1    |   wo   |   0x0   | pkt_sent        | Write 1 to force [`INTR_STATE.pkt_sent`](#intr_state) to 1.        |
|   0    |   wo   |   0x0   | pkt_received    | Write 1 to force [`INTR_STATE.pkt_received`](#intr_state) to 1.    |

## ALERT_TEST
Alert Test Register
- Offset: `0xc`
- Reset default: `0x0`
- Reset mask: `0x1`

### Fields

```wavejson
{"reg": [{"name": "fatal_fault", "bits": 1, "attr": ["wo"], "rotate": -90}, {"bits": 31}], "config": {"lanes": 1, "fontsize": 10, "vspace": 130}}
```

|  Bits  |  Type  |  Reset  | Name        | Description                                      |
|:------:|:------:|:-------:|:------------|:-------------------------------------------------|
|  31:1  |        |         |             | Reserved                                         |
|   0    |   wo   |   0x0   | fatal_fault | Write 1 to trigger one alert event of this kind. |

## usbctrl
USB Control
- Offset: `0x10`
- Reset default: `0x0`
- Reset mask: `0x7f0003`

### Fields

```wavejson
{"reg": [{"name": "enable", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "resume_link_active", "bits": 1, "attr": ["wo"], "rotate": -90}, {"bits": 14}, {"name": "device_address", "bits": 7, "attr": ["rw"], "rotate": -90}, {"bits": 9}], "config": {"lanes": 1, "fontsize": 10, "vspace": 200}}
```

|  Bits  |  Type  |  Reset  | Name               | Description                                                                                                                                                                                                                                            |
|:------:|:------:|:-------:|:-------------------|:-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------|
| 31:23  |        |         |                    | Reserved                                                                                                                                                                                                                                               |
| 22:16  |   rw   |   0x0   | device_address     | Device address set by host (this should be copied from the Set Device ID SETUP packet). This will be zeroed by the hardware when the link resets.                                                                                                      |
|  15:2  |        |         |                    | Reserved                                                                                                                                                                                                                                               |
|   1    |   wo   |   0x0   | resume_link_active | Write a 1 to this bit to instruct usbdev to jump to the LinkResuming state. The write will only have an effect when the device is in the LinkPowered state. Its intention is to handle a resume-from-suspend event after the IP has been powered down. |
|   0    |   rw   |   0x0   | enable             | Set to connect the USB interface (i.e. assert the pullup).                                                                                                                                                                                             |

## ep_out_enable
Enable an endpoint to respond to transactions in the downstream direction.
Note that as the default endpoint, endpoint 0 must be enabled in both the IN and OUT directions before enabling the USB interface to connect.
- Offset: `0x14`
- Reset default: `0x0`
- Reset mask: `0xfff`

### Fields

```wavejson
{"reg": [{"name": "enable_0", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "enable_1", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "enable_2", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "enable_3", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "enable_4", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "enable_5", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "enable_6", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "enable_7", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "enable_8", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "enable_9", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "enable_10", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "enable_11", "bits": 1, "attr": ["rw"], "rotate": -90}, {"bits": 20}], "config": {"lanes": 1, "fontsize": 10, "vspace": 110}}
```

|  Bits  |  Type  |  Reset  | Name      | Description                                                                                                                                                                                     |
|:------:|:------:|:-------:|:----------|:------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------|
| 31:12  |        |         |           | Reserved                                                                                                                                                                                        |
|   11   |   rw   |   0x0   | enable_11 | This bit must be set to enable downstream transactions to be received on the endpoint and elicit responses. If the bit is clear, any SETUP or OUT packets sent to the endpoint will be ignored. |
|   10   |   rw   |   0x0   | enable_10 | This bit must be set to enable downstream transactions to be received on the endpoint and elicit responses. If the bit is clear, any SETUP or OUT packets sent to the endpoint will be ignored. |
|   9    |   rw   |   0x0   | enable_9  | This bit must be set to enable downstream transactions to be received on the endpoint and elicit responses. If the bit is clear, any SETUP or OUT packets sent to the endpoint will be ignored. |
|   8    |   rw   |   0x0   | enable_8  | This bit must be set to enable downstream transactions to be received on the endpoint and elicit responses. If the bit is clear, any SETUP or OUT packets sent to the endpoint will be ignored. |
|   7    |   rw   |   0x0   | enable_7  | This bit must be set to enable downstream transactions to be received on the endpoint and elicit responses. If the bit is clear, any SETUP or OUT packets sent to the endpoint will be ignored. |
|   6    |   rw   |   0x0   | enable_6  | This bit must be set to enable downstream transactions to be received on the endpoint and elicit responses. If the bit is clear, any SETUP or OUT packets sent to the endpoint will be ignored. |
|   5    |   rw   |   0x0   | enable_5  | This bit must be set to enable downstream transactions to be received on the endpoint and elicit responses. If the bit is clear, any SETUP or OUT packets sent to the endpoint will be ignored. |
|   4    |   rw   |   0x0   | enable_4  | This bit must be set to enable downstream transactions to be received on the endpoint and elicit responses. If the bit is clear, any SETUP or OUT packets sent to the endpoint will be ignored. |
|   3    |   rw   |   0x0   | enable_3  | This bit must be set to enable downstream transactions to be received on the endpoint and elicit responses. If the bit is clear, any SETUP or OUT packets sent to the endpoint will be ignored. |
|   2    |   rw   |   0x0   | enable_2  | This bit must be set to enable downstream transactions to be received on the endpoint and elicit responses. If the bit is clear, any SETUP or OUT packets sent to the endpoint will be ignored. |
|   1    |   rw   |   0x0   | enable_1  | This bit must be set to enable downstream transactions to be received on the endpoint and elicit responses. If the bit is clear, any SETUP or OUT packets sent to the endpoint will be ignored. |
|   0    |   rw   |   0x0   | enable_0  | This bit must be set to enable downstream transactions to be received on the endpoint and elicit responses. If the bit is clear, any SETUP or OUT packets sent to the endpoint will be ignored. |

## ep_in_enable
Enable an endpoint to respond to transactions in the upstream direction.
Note that as the default endpoint, endpoint 0 must be enabled in both the IN and OUT directions before enabling the USB interface to connect.
- Offset: `0x18`
- Reset default: `0x0`
- Reset mask: `0xfff`

### Fields

```wavejson
{"reg": [{"name": "enable_0", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "enable_1", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "enable_2", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "enable_3", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "enable_4", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "enable_5", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "enable_6", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "enable_7", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "enable_8", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "enable_9", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "enable_10", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "enable_11", "bits": 1, "attr": ["rw"], "rotate": -90}, {"bits": 20}], "config": {"lanes": 1, "fontsize": 10, "vspace": 110}}
```

|  Bits  |  Type  |  Reset  | Name      | Description                                                                                                                                                                             |
|:------:|:------:|:-------:|:----------|:----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------|
| 31:12  |        |         |           | Reserved                                                                                                                                                                                |
|   11   |   rw   |   0x0   | enable_11 | This bit must be set to enable upstream transactions to be received on the endpoint and elicit responses. If the bit is clear then any IN packets sent to the endpoint will be ignored. |
|   10   |   rw   |   0x0   | enable_10 | This bit must be set to enable upstream transactions to be received on the endpoint and elicit responses. If the bit is clear then any IN packets sent to the endpoint will be ignored. |
|   9    |   rw   |   0x0   | enable_9  | This bit must be set to enable upstream transactions to be received on the endpoint and elicit responses. If the bit is clear then any IN packets sent to the endpoint will be ignored. |
|   8    |   rw   |   0x0   | enable_8  | This bit must be set to enable upstream transactions to be received on the endpoint and elicit responses. If the bit is clear then any IN packets sent to the endpoint will be ignored. |
|   7    |   rw   |   0x0   | enable_7  | This bit must be set to enable upstream transactions to be received on the endpoint and elicit responses. If the bit is clear then any IN packets sent to the endpoint will be ignored. |
|   6    |   rw   |   0x0   | enable_6  | This bit must be set to enable upstream transactions to be received on the endpoint and elicit responses. If the bit is clear then any IN packets sent to the endpoint will be ignored. |
|   5    |   rw   |   0x0   | enable_5  | This bit must be set to enable upstream transactions to be received on the endpoint and elicit responses. If the bit is clear then any IN packets sent to the endpoint will be ignored. |
|   4    |   rw   |   0x0   | enable_4  | This bit must be set to enable upstream transactions to be received on the endpoint and elicit responses. If the bit is clear then any IN packets sent to the endpoint will be ignored. |
|   3    |   rw   |   0x0   | enable_3  | This bit must be set to enable upstream transactions to be received on the endpoint and elicit responses. If the bit is clear then any IN packets sent to the endpoint will be ignored. |
|   2    |   rw   |   0x0   | enable_2  | This bit must be set to enable upstream transactions to be received on the endpoint and elicit responses. If the bit is clear then any IN packets sent to the endpoint will be ignored. |
|   1    |   rw   |   0x0   | enable_1  | This bit must be set to enable upstream transactions to be received on the endpoint and elicit responses. If the bit is clear then any IN packets sent to the endpoint will be ignored. |
|   0    |   rw   |   0x0   | enable_0  | This bit must be set to enable upstream transactions to be received on the endpoint and elicit responses. If the bit is clear then any IN packets sent to the endpoint will be ignored. |

## usbstat
USB Status
- Offset: `0x1c`
- Reset default: `0x80000000`
- Reset mask: `0xcfffffff`

### Fields

```wavejson
{"reg": [{"name": "frame", "bits": 11, "attr": ["ro"], "rotate": 0}, {"name": "host_lost", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "link_state", "bits": 3, "attr": ["ro"], "rotate": -90}, {"name": "sense", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "av_out_depth", "bits": 4, "attr": ["ro"], "rotate": -90}, {"name": "av_setup_depth", "bits": 3, "attr": ["ro"], "rotate": -90}, {"name": "av_out_full", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "rx_depth", "bits": 4, "attr": ["ro"], "rotate": -90}, {"bits": 2}, {"name": "av_setup_full", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "rx_empty", "bits": 1, "attr": ["ro"], "rotate": -90}], "config": {"lanes": 1, "fontsize": 10, "vspace": 160}}
```

|  Bits  |  Type  |  Reset  | Name                                       |
|:------:|:------:|:-------:|:-------------------------------------------|
|   31   |   ro   |   0x1   | [rx_empty](#usbstat--rx_empty)             |
|   30   |   ro   |    x    | [av_setup_full](#usbstat--av_setup_full)   |
| 29:28  |        |         | Reserved                                   |
| 27:24  |   ro   |    x    | [rx_depth](#usbstat--rx_depth)             |
|   23   |   ro   |    x    | [av_out_full](#usbstat--av_out_full)       |
| 22:20  |   ro   |    x    | [av_setup_depth](#usbstat--av_setup_depth) |
| 19:16  |   ro   |    x    | [av_out_depth](#usbstat--av_out_depth)     |
|   15   |   ro   |    x    | [sense](#usbstat--sense)                   |
| 14:12  |   ro   |    x    | [link_state](#usbstat--link_state)         |
|   11   |   ro   |    x    | [host_lost](#usbstat--host_lost)           |
|  10:0  |   ro   |    x    | [frame](#usbstat--frame)                   |

### usbstat . rx_empty
Received Buffer FIFO is empty.

### usbstat . av_setup_full
Available SETUP Buffer FIFO is full.

### usbstat . rx_depth
Number of buffers in the Received Buffer FIFO.

These buffers have packets that have been received and
should be popped from the FIFO and processed.

### usbstat . av_out_full
Available OUT Buffer FIFO is full.

### usbstat . av_setup_depth
Number of buffers in the Available SETUP Buffer FIFO.

These buffers are available for receiving SETUP DATA packets.

### usbstat . av_out_depth
Number of buffers in the Available OUT Buffer FIFO.

These buffers are available for receiving OUT DATA packets.

### usbstat . sense
Reflects the state of the sense pin.
1 indicates that the host is providing VBUS.
Note that this bit always shows the state of the actual pin and is unaffected by the direct pin driving in phy_pins_drive.

### usbstat . link_state
State of USB link, decoded from line.

| Value   | Name              | Description                                                                     |
|:--------|:------------------|:--------------------------------------------------------------------------------|
| 0x0     | disconnected      | Link disconnected (no VBUS or no pull-up connected)                             |
| 0x1     | powered           | Link powered and connected, but not reset yet                                   |
| 0x2     | powered_suspended | Link suspended (constant idle/J for > 3 ms), but not reset yet                  |
| 0x3     | active            | Link active                                                                     |
| 0x4     | suspended         | Link suspended (constant idle for > 3 ms), was active before becoming suspended |
| 0x5     | active_nosof      | Link active but no SOF has been received since the last reset.                  |
| 0x6     | resuming          | Link resuming to an active state, pending the end of resume signaling           |

Other values are reserved.

### usbstat . host_lost
Start of frame not received from host for 4.096 ms and the line is active.

### usbstat . frame
Frame index received from host. On an active link, this will increment every millisecond.

## avoutbuffer
Available OUT Buffer FIFO
- Offset: `0x20`
- Reset default: `0x0`
- Reset mask: `0x1f`

### Fields

```wavejson
{"reg": [{"name": "buffer", "bits": 5, "attr": ["wo"], "rotate": 0}, {"bits": 27}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name   | Description                                                                                                                                             |
|:------:|:------:|:-------:|:-------|:--------------------------------------------------------------------------------------------------------------------------------------------------------|
|  31:5  |        |         |        | Reserved                                                                                                                                                |
|  4:0   |   wo   |    x    | buffer | This field contains the buffer ID being passed to the USB receive engine. If the Available OUT Buffer FIFO is full, any write operations are discarded. |

## avsetupbuffer
Available SETUP Buffer FIFO
- Offset: `0x24`
- Reset default: `0x0`
- Reset mask: `0x1f`

### Fields

```wavejson
{"reg": [{"name": "buffer", "bits": 5, "attr": ["wo"], "rotate": 0}, {"bits": 27}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name   | Description                                                                                                                                               |
|:------:|:------:|:-------:|:-------|:----------------------------------------------------------------------------------------------------------------------------------------------------------|
|  31:5  |        |         |        | Reserved                                                                                                                                                  |
|  4:0   |   wo   |    x    | buffer | This field contains the buffer ID being passed to the USB receive engine. If the Available SETUP Buffer FIFO is full, any write operations are discarded. |

## rxfifo
Received Buffer FIFO
- Offset: `0x28`
- Reset default: `0x0`
- Reset mask: `0xf87f1f`

### Fields

```wavejson
{"reg": [{"name": "buffer", "bits": 5, "attr": ["ro"], "rotate": 0}, {"bits": 3}, {"name": "size", "bits": 7, "attr": ["ro"], "rotate": 0}, {"bits": 4}, {"name": "setup", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "ep", "bits": 4, "attr": ["ro"], "rotate": 0}, {"bits": 8}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name   | Description                                                                                                                                            |
|:------:|:------:|:-------:|:-------|:-------------------------------------------------------------------------------------------------------------------------------------------------------|
| 31:24  |        |         |        | Reserved                                                                                                                                               |
| 23:20  |   ro   |    x    | ep     | This field contains the endpoint ID to which the packet was directed.                                                                                  |
|   19   |   ro   |    x    | setup  | This bit indicates if the received transaction is of type SETUP (1) or OUT (0).                                                                        |
| 18:15  |        |         |        | Reserved                                                                                                                                               |
|  14:8  |   ro   |    x    | size   | This field contains the data length in bytes of the packet written to the buffer.                                                                      |
|  7:5   |        |         |        | Reserved                                                                                                                                               |
|  4:0   |   ro   |    x    | buffer | This field contains the buffer ID that data was received into. On read the buffer ID is popped from the Received Buffer FIFO and returned to software. |

## rxenable_setup
Receive SETUP transaction enable
- Offset: `0x2c`
- Reset default: `0x0`
- Reset mask: `0xfff`

### Fields

```wavejson
{"reg": [{"name": "setup_0", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "setup_1", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "setup_2", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "setup_3", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "setup_4", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "setup_5", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "setup_6", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "setup_7", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "setup_8", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "setup_9", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "setup_10", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "setup_11", "bits": 1, "attr": ["rw"], "rotate": -90}, {"bits": 20}], "config": {"lanes": 1, "fontsize": 10, "vspace": 100}}
```

|  Bits  |  Type  |  Reset  | Name     | Description                                                                                                                                                                                                          |
|:------:|:------:|:-------:|:---------|:---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------|
| 31:12  |        |         |          | Reserved                                                                                                                                                                                                             |
|   11   |   rw   |   0x0   | setup_11 | This bit must be set to enable SETUP transactions to be received on the endpoint. If the bit is clear then a SETUP packet will be ignored. The bit should be set for control endpoints (and only control endpoints). |
|   10   |   rw   |   0x0   | setup_10 | This bit must be set to enable SETUP transactions to be received on the endpoint. If the bit is clear then a SETUP packet will be ignored. The bit should be set for control endpoints (and only control endpoints). |
|   9    |   rw   |   0x0   | setup_9  | This bit must be set to enable SETUP transactions to be received on the endpoint. If the bit is clear then a SETUP packet will be ignored. The bit should be set for control endpoints (and only control endpoints). |
|   8    |   rw   |   0x0   | setup_8  | This bit must be set to enable SETUP transactions to be received on the endpoint. If the bit is clear then a SETUP packet will be ignored. The bit should be set for control endpoints (and only control endpoints). |
|   7    |   rw   |   0x0   | setup_7  | This bit must be set to enable SETUP transactions to be received on the endpoint. If the bit is clear then a SETUP packet will be ignored. The bit should be set for control endpoints (and only control endpoints). |
|   6    |   rw   |   0x0   | setup_6  | This bit must be set to enable SETUP transactions to be received on the endpoint. If the bit is clear then a SETUP packet will be ignored. The bit should be set for control endpoints (and only control endpoints). |
|   5    |   rw   |   0x0   | setup_5  | This bit must be set to enable SETUP transactions to be received on the endpoint. If the bit is clear then a SETUP packet will be ignored. The bit should be set for control endpoints (and only control endpoints). |
|   4    |   rw   |   0x0   | setup_4  | This bit must be set to enable SETUP transactions to be received on the endpoint. If the bit is clear then a SETUP packet will be ignored. The bit should be set for control endpoints (and only control endpoints). |
|   3    |   rw   |   0x0   | setup_3  | This bit must be set to enable SETUP transactions to be received on the endpoint. If the bit is clear then a SETUP packet will be ignored. The bit should be set for control endpoints (and only control endpoints). |
|   2    |   rw   |   0x0   | setup_2  | This bit must be set to enable SETUP transactions to be received on the endpoint. If the bit is clear then a SETUP packet will be ignored. The bit should be set for control endpoints (and only control endpoints). |
|   1    |   rw   |   0x0   | setup_1  | This bit must be set to enable SETUP transactions to be received on the endpoint. If the bit is clear then a SETUP packet will be ignored. The bit should be set for control endpoints (and only control endpoints). |
|   0    |   rw   |   0x0   | setup_0  | This bit must be set to enable SETUP transactions to be received on the endpoint. If the bit is clear then a SETUP packet will be ignored. The bit should be set for control endpoints (and only control endpoints). |

## rxenable_out
Receive OUT transaction enable
- Offset: `0x30`
- Reset default: `0x0`
- Reset mask: `0xfff0fff`

### Fields

```wavejson
{"reg": [{"name": "out", "bits": 12, "attr": ["rw"], "rotate": 0}, {"bits": 4}, {"name": "preserve", "bits": 12, "attr": ["wo"], "rotate": 0}, {"bits": 4}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name                                |
|:------:|:------:|:-------:|:------------------------------------|
| 31:28  |        |         | Reserved                            |
| 27:16  |   wo   |    x    | [preserve](#rxenable_out--preserve) |
| 15:12  |        |         | Reserved                            |
|  11:0  |   rw   |    x    | [out](#rxenable_out--out)           |

### rxenable_out . preserve
When writing to this register, only those 'out' bits with a corresponding 'preserve' bit of 0 are updated.
The 'preserve' field should therefore normally be set to all '1s', except for those bits that the software wishes to modify.
This conditional update facility avoids a race with the hardware when it is clearing the 'out' bit for another enabled endpoint.

### rxenable_out . out
This bit must be set to enable OUT transactions to be received on the endpoint.
If the bit is clear but the endpoint is enabled, then an OUT request will receive a NAK in response.
If set_nak_out for this endpoint is set, hardware will clear this bit whenever an OUT transaction is received on this endpoint.
Software must set this bit again to receive the next OUT transaction.
Until that happens, hardware will continue to NAK any OUT transactions to this endpoint.

## set_nak_out
Set NAK after OUT transactions
- Offset: `0x34`
- Reset default: `0x0`
- Reset mask: `0xfff`

### Fields

```wavejson
{"reg": [{"name": "enable_0", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "enable_1", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "enable_2", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "enable_3", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "enable_4", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "enable_5", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "enable_6", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "enable_7", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "enable_8", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "enable_9", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "enable_10", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "enable_11", "bits": 1, "attr": ["rw"], "rotate": -90}, {"bits": 20}], "config": {"lanes": 1, "fontsize": 10, "vspace": 110}}
```

|  Bits  |  Type  |  Reset  | Name      | Description                                                                                                                                                                                       |
|:------:|:------:|:-------:|:----------|:--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------|
| 31:12  |        |         |           | Reserved                                                                                                                                                                                          |
|   11   |   rw   |   0x0   | enable_11 | When this bit is set, hardware will clear this endpoint's rxenable_out bit whenever an OUT transaction is received on this endpoint. This bit should not be changed while the endpoint is active. |
|   10   |   rw   |   0x0   | enable_10 | When this bit is set, hardware will clear this endpoint's rxenable_out bit whenever an OUT transaction is received on this endpoint. This bit should not be changed while the endpoint is active. |
|   9    |   rw   |   0x0   | enable_9  | When this bit is set, hardware will clear this endpoint's rxenable_out bit whenever an OUT transaction is received on this endpoint. This bit should not be changed while the endpoint is active. |
|   8    |   rw   |   0x0   | enable_8  | When this bit is set, hardware will clear this endpoint's rxenable_out bit whenever an OUT transaction is received on this endpoint. This bit should not be changed while the endpoint is active. |
|   7    |   rw   |   0x0   | enable_7  | When this bit is set, hardware will clear this endpoint's rxenable_out bit whenever an OUT transaction is received on this endpoint. This bit should not be changed while the endpoint is active. |
|   6    |   rw   |   0x0   | enable_6  | When this bit is set, hardware will clear this endpoint's rxenable_out bit whenever an OUT transaction is received on this endpoint. This bit should not be changed while the endpoint is active. |
|   5    |   rw   |   0x0   | enable_5  | When this bit is set, hardware will clear this endpoint's rxenable_out bit whenever an OUT transaction is received on this endpoint. This bit should not be changed while the endpoint is active. |
|   4    |   rw   |   0x0   | enable_4  | When this bit is set, hardware will clear this endpoint's rxenable_out bit whenever an OUT transaction is received on this endpoint. This bit should not be changed while the endpoint is active. |
|   3    |   rw   |   0x0   | enable_3  | When this bit is set, hardware will clear this endpoint's rxenable_out bit whenever an OUT transaction is received on this endpoint. This bit should not be changed while the endpoint is active. |
|   2    |   rw   |   0x0   | enable_2  | When this bit is set, hardware will clear this endpoint's rxenable_out bit whenever an OUT transaction is received on this endpoint. This bit should not be changed while the endpoint is active. |
|   1    |   rw   |   0x0   | enable_1  | When this bit is set, hardware will clear this endpoint's rxenable_out bit whenever an OUT transaction is received on this endpoint. This bit should not be changed while the endpoint is active. |
|   0    |   rw   |   0x0   | enable_0  | When this bit is set, hardware will clear this endpoint's rxenable_out bit whenever an OUT transaction is received on this endpoint. This bit should not be changed while the endpoint is active. |

## in_sent
IN Transaction Sent
- Offset: `0x38`
- Reset default: `0x0`
- Reset mask: `0xfff`

### Fields

```wavejson
{"reg": [{"name": "sent_0", "bits": 1, "attr": ["rw1c"], "rotate": -90}, {"name": "sent_1", "bits": 1, "attr": ["rw1c"], "rotate": -90}, {"name": "sent_2", "bits": 1, "attr": ["rw1c"], "rotate": -90}, {"name": "sent_3", "bits": 1, "attr": ["rw1c"], "rotate": -90}, {"name": "sent_4", "bits": 1, "attr": ["rw1c"], "rotate": -90}, {"name": "sent_5", "bits": 1, "attr": ["rw1c"], "rotate": -90}, {"name": "sent_6", "bits": 1, "attr": ["rw1c"], "rotate": -90}, {"name": "sent_7", "bits": 1, "attr": ["rw1c"], "rotate": -90}, {"name": "sent_8", "bits": 1, "attr": ["rw1c"], "rotate": -90}, {"name": "sent_9", "bits": 1, "attr": ["rw1c"], "rotate": -90}, {"name": "sent_10", "bits": 1, "attr": ["rw1c"], "rotate": -90}, {"name": "sent_11", "bits": 1, "attr": ["rw1c"], "rotate": -90}, {"bits": 20}], "config": {"lanes": 1, "fontsize": 10, "vspace": 90}}
```

|  Bits  |  Type  |  Reset  | Name    | Description                                                                                                                      |
|:------:|:------:|:-------:|:--------|:---------------------------------------------------------------------------------------------------------------------------------|
| 31:12  |        |         |         | Reserved                                                                                                                         |
|   11   |  rw1c  |   0x0   | sent_11 | This bit will be set when the ACK is received from the host to indicate successful packet delivery as part of an IN transaction. |
|   10   |  rw1c  |   0x0   | sent_10 | This bit will be set when the ACK is received from the host to indicate successful packet delivery as part of an IN transaction. |
|   9    |  rw1c  |   0x0   | sent_9  | This bit will be set when the ACK is received from the host to indicate successful packet delivery as part of an IN transaction. |
|   8    |  rw1c  |   0x0   | sent_8  | This bit will be set when the ACK is received from the host to indicate successful packet delivery as part of an IN transaction. |
|   7    |  rw1c  |   0x0   | sent_7  | This bit will be set when the ACK is received from the host to indicate successful packet delivery as part of an IN transaction. |
|   6    |  rw1c  |   0x0   | sent_6  | This bit will be set when the ACK is received from the host to indicate successful packet delivery as part of an IN transaction. |
|   5    |  rw1c  |   0x0   | sent_5  | This bit will be set when the ACK is received from the host to indicate successful packet delivery as part of an IN transaction. |
|   4    |  rw1c  |   0x0   | sent_4  | This bit will be set when the ACK is received from the host to indicate successful packet delivery as part of an IN transaction. |
|   3    |  rw1c  |   0x0   | sent_3  | This bit will be set when the ACK is received from the host to indicate successful packet delivery as part of an IN transaction. |
|   2    |  rw1c  |   0x0   | sent_2  | This bit will be set when the ACK is received from the host to indicate successful packet delivery as part of an IN transaction. |
|   1    |  rw1c  |   0x0   | sent_1  | This bit will be set when the ACK is received from the host to indicate successful packet delivery as part of an IN transaction. |
|   0    |  rw1c  |   0x0   | sent_0  | This bit will be set when the ACK is received from the host to indicate successful packet delivery as part of an IN transaction. |

## out_stall
OUT Endpoint STALL control
- Offset: `0x3c`
- Reset default: `0x0`
- Reset mask: `0xfff`

### Fields

```wavejson
{"reg": [{"name": "endpoint_0", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "endpoint_1", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "endpoint_2", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "endpoint_3", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "endpoint_4", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "endpoint_5", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "endpoint_6", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "endpoint_7", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "endpoint_8", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "endpoint_9", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "endpoint_10", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "endpoint_11", "bits": 1, "attr": ["rw"], "rotate": -90}, {"bits": 20}], "config": {"lanes": 1, "fontsize": 10, "vspace": 130}}
```

|  Bits  |  Type  |  Reset  | Name                                   |
|:------:|:------:|:-------:|:---------------------------------------|
| 31:12  |        |         | Reserved                               |
|   11   |   rw   |   0x0   | [endpoint_11](#out_stall--endpoint_11) |
|   10   |   rw   |   0x0   | [endpoint_10](#out_stall--endpoint_10) |
|   9    |   rw   |   0x0   | [endpoint_9](#out_stall--endpoint_9)   |
|   8    |   rw   |   0x0   | [endpoint_8](#out_stall--endpoint_8)   |
|   7    |   rw   |   0x0   | [endpoint_7](#out_stall--endpoint_7)   |
|   6    |   rw   |   0x0   | [endpoint_6](#out_stall--endpoint_6)   |
|   5    |   rw   |   0x0   | [endpoint_5](#out_stall--endpoint_5)   |
|   4    |   rw   |   0x0   | [endpoint_4](#out_stall--endpoint_4)   |
|   3    |   rw   |   0x0   | [endpoint_3](#out_stall--endpoint_3)   |
|   2    |   rw   |   0x0   | [endpoint_2](#out_stall--endpoint_2)   |
|   1    |   rw   |   0x0   | [endpoint_1](#out_stall--endpoint_1)   |
|   0    |   rw   |   0x0   | [endpoint_0](#out_stall--endpoint_0)   |

### out_stall . endpoint_11
If this bit is set then an OUT transaction to this endpoint will elicit a STALL handshake, when a non-isochronous endpoint is enabled.
If the configuration has both STALL and NAK enabled, the STALL handshake will take priority.

Note that SETUP transactions are always either accepted or ignored.
For endpoints that accept SETUP transactions, a SETUP packet will clear the STALL flag on endpoints for both the IN and OUT directions.

### out_stall . endpoint_10
If this bit is set then an OUT transaction to this endpoint will elicit a STALL handshake, when a non-isochronous endpoint is enabled.
If the configuration has both STALL and NAK enabled, the STALL handshake will take priority.

Note that SETUP transactions are always either accepted or ignored.
For endpoints that accept SETUP transactions, a SETUP packet will clear the STALL flag on endpoints for both the IN and OUT directions.

### out_stall . endpoint_9
If this bit is set then an OUT transaction to this endpoint will elicit a STALL handshake, when a non-isochronous endpoint is enabled.
If the configuration has both STALL and NAK enabled, the STALL handshake will take priority.

Note that SETUP transactions are always either accepted or ignored.
For endpoints that accept SETUP transactions, a SETUP packet will clear the STALL flag on endpoints for both the IN and OUT directions.

### out_stall . endpoint_8
If this bit is set then an OUT transaction to this endpoint will elicit a STALL handshake, when a non-isochronous endpoint is enabled.
If the configuration has both STALL and NAK enabled, the STALL handshake will take priority.

Note that SETUP transactions are always either accepted or ignored.
For endpoints that accept SETUP transactions, a SETUP packet will clear the STALL flag on endpoints for both the IN and OUT directions.

### out_stall . endpoint_7
If this bit is set then an OUT transaction to this endpoint will elicit a STALL handshake, when a non-isochronous endpoint is enabled.
If the configuration has both STALL and NAK enabled, the STALL handshake will take priority.

Note that SETUP transactions are always either accepted or ignored.
For endpoints that accept SETUP transactions, a SETUP packet will clear the STALL flag on endpoints for both the IN and OUT directions.

### out_stall . endpoint_6
If this bit is set then an OUT transaction to this endpoint will elicit a STALL handshake, when a non-isochronous endpoint is enabled.
If the configuration has both STALL and NAK enabled, the STALL handshake will take priority.

Note that SETUP transactions are always either accepted or ignored.
For endpoints that accept SETUP transactions, a SETUP packet will clear the STALL flag on endpoints for both the IN and OUT directions.

### out_stall . endpoint_5
If this bit is set then an OUT transaction to this endpoint will elicit a STALL handshake, when a non-isochronous endpoint is enabled.
If the configuration has both STALL and NAK enabled, the STALL handshake will take priority.

Note that SETUP transactions are always either accepted or ignored.
For endpoints that accept SETUP transactions, a SETUP packet will clear the STALL flag on endpoints for both the IN and OUT directions.

### out_stall . endpoint_4
If this bit is set then an OUT transaction to this endpoint will elicit a STALL handshake, when a non-isochronous endpoint is enabled.
If the configuration has both STALL and NAK enabled, the STALL handshake will take priority.

Note that SETUP transactions are always either accepted or ignored.
For endpoints that accept SETUP transactions, a SETUP packet will clear the STALL flag on endpoints for both the IN and OUT directions.

### out_stall . endpoint_3
If this bit is set then an OUT transaction to this endpoint will elicit a STALL handshake, when a non-isochronous endpoint is enabled.
If the configuration has both STALL and NAK enabled, the STALL handshake will take priority.

Note that SETUP transactions are always either accepted or ignored.
For endpoints that accept SETUP transactions, a SETUP packet will clear the STALL flag on endpoints for both the IN and OUT directions.

### out_stall . endpoint_2
If this bit is set then an OUT transaction to this endpoint will elicit a STALL handshake, when a non-isochronous endpoint is enabled.
If the configuration has both STALL and NAK enabled, the STALL handshake will take priority.

Note that SETUP transactions are always either accepted or ignored.
For endpoints that accept SETUP transactions, a SETUP packet will clear the STALL flag on endpoints for both the IN and OUT directions.

### out_stall . endpoint_1
If this bit is set then an OUT transaction to this endpoint will elicit a STALL handshake, when a non-isochronous endpoint is enabled.
If the configuration has both STALL and NAK enabled, the STALL handshake will take priority.

Note that SETUP transactions are always either accepted or ignored.
For endpoints that accept SETUP transactions, a SETUP packet will clear the STALL flag on endpoints for both the IN and OUT directions.

### out_stall . endpoint_0
If this bit is set then an OUT transaction to this endpoint will elicit a STALL handshake, when a non-isochronous endpoint is enabled.
If the configuration has both STALL and NAK enabled, the STALL handshake will take priority.

Note that SETUP transactions are always either accepted or ignored.
For endpoints that accept SETUP transactions, a SETUP packet will clear the STALL flag on endpoints for both the IN and OUT directions.

## in_stall
IN Endpoint STALL control
- Offset: `0x40`
- Reset default: `0x0`
- Reset mask: `0xfff`

### Fields

```wavejson
{"reg": [{"name": "endpoint_0", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "endpoint_1", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "endpoint_2", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "endpoint_3", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "endpoint_4", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "endpoint_5", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "endpoint_6", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "endpoint_7", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "endpoint_8", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "endpoint_9", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "endpoint_10", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "endpoint_11", "bits": 1, "attr": ["rw"], "rotate": -90}, {"bits": 20}], "config": {"lanes": 1, "fontsize": 10, "vspace": 130}}
```

|  Bits  |  Type  |  Reset  | Name                                  |
|:------:|:------:|:-------:|:--------------------------------------|
| 31:12  |        |         | Reserved                              |
|   11   |   rw   |   0x0   | [endpoint_11](#in_stall--endpoint_11) |
|   10   |   rw   |   0x0   | [endpoint_10](#in_stall--endpoint_10) |
|   9    |   rw   |   0x0   | [endpoint_9](#in_stall--endpoint_9)   |
|   8    |   rw   |   0x0   | [endpoint_8](#in_stall--endpoint_8)   |
|   7    |   rw   |   0x0   | [endpoint_7](#in_stall--endpoint_7)   |
|   6    |   rw   |   0x0   | [endpoint_6](#in_stall--endpoint_6)   |
|   5    |   rw   |   0x0   | [endpoint_5](#in_stall--endpoint_5)   |
|   4    |   rw   |   0x0   | [endpoint_4](#in_stall--endpoint_4)   |
|   3    |   rw   |   0x0   | [endpoint_3](#in_stall--endpoint_3)   |
|   2    |   rw   |   0x0   | [endpoint_2](#in_stall--endpoint_2)   |
|   1    |   rw   |   0x0   | [endpoint_1](#in_stall--endpoint_1)   |
|   0    |   rw   |   0x0   | [endpoint_0](#in_stall--endpoint_0)   |

### in_stall . endpoint_11
If this bit is set then an IN transaction to this endpoint will elicit a STALL handshake, when a non-isochronous endpoint is enabled.
If the configuration has both STALL and NAK enabled, the STALL handshake will take priority.

Note that SETUP transactions are always either accepted or ignored.
For endpoints that accept SETUP transactions, a SETUP packet will clear the STALL flag on endpoints for both the IN and OUT directions.

### in_stall . endpoint_10
If this bit is set then an IN transaction to this endpoint will elicit a STALL handshake, when a non-isochronous endpoint is enabled.
If the configuration has both STALL and NAK enabled, the STALL handshake will take priority.

Note that SETUP transactions are always either accepted or ignored.
For endpoints that accept SETUP transactions, a SETUP packet will clear the STALL flag on endpoints for both the IN and OUT directions.

### in_stall . endpoint_9
If this bit is set then an IN transaction to this endpoint will elicit a STALL handshake, when a non-isochronous endpoint is enabled.
If the configuration has both STALL and NAK enabled, the STALL handshake will take priority.

Note that SETUP transactions are always either accepted or ignored.
For endpoints that accept SETUP transactions, a SETUP packet will clear the STALL flag on endpoints for both the IN and OUT directions.

### in_stall . endpoint_8
If this bit is set then an IN transaction to this endpoint will elicit a STALL handshake, when a non-isochronous endpoint is enabled.
If the configuration has both STALL and NAK enabled, the STALL handshake will take priority.

Note that SETUP transactions are always either accepted or ignored.
For endpoints that accept SETUP transactions, a SETUP packet will clear the STALL flag on endpoints for both the IN and OUT directions.

### in_stall . endpoint_7
If this bit is set then an IN transaction to this endpoint will elicit a STALL handshake, when a non-isochronous endpoint is enabled.
If the configuration has both STALL and NAK enabled, the STALL handshake will take priority.

Note that SETUP transactions are always either accepted or ignored.
For endpoints that accept SETUP transactions, a SETUP packet will clear the STALL flag on endpoints for both the IN and OUT directions.

### in_stall . endpoint_6
If this bit is set then an IN transaction to this endpoint will elicit a STALL handshake, when a non-isochronous endpoint is enabled.
If the configuration has both STALL and NAK enabled, the STALL handshake will take priority.

Note that SETUP transactions are always either accepted or ignored.
For endpoints that accept SETUP transactions, a SETUP packet will clear the STALL flag on endpoints for both the IN and OUT directions.

### in_stall . endpoint_5
If this bit is set then an IN transaction to this endpoint will elicit a STALL handshake, when a non-isochronous endpoint is enabled.
If the configuration has both STALL and NAK enabled, the STALL handshake will take priority.

Note that SETUP transactions are always either accepted or ignored.
For endpoints that accept SETUP transactions, a SETUP packet will clear the STALL flag on endpoints for both the IN and OUT directions.

### in_stall . endpoint_4
If this bit is set then an IN transaction to this endpoint will elicit a STALL handshake, when a non-isochronous endpoint is enabled.
If the configuration has both STALL and NAK enabled, the STALL handshake will take priority.

Note that SETUP transactions are always either accepted or ignored.
For endpoints that accept SETUP transactions, a SETUP packet will clear the STALL flag on endpoints for both the IN and OUT directions.

### in_stall . endpoint_3
If this bit is set then an IN transaction to this endpoint will elicit a STALL handshake, when a non-isochronous endpoint is enabled.
If the configuration has both STALL and NAK enabled, the STALL handshake will take priority.

Note that SETUP transactions are always either accepted or ignored.
For endpoints that accept SETUP transactions, a SETUP packet will clear the STALL flag on endpoints for both the IN and OUT directions.

### in_stall . endpoint_2
If this bit is set then an IN transaction to this endpoint will elicit a STALL handshake, when a non-isochronous endpoint is enabled.
If the configuration has both STALL and NAK enabled, the STALL handshake will take priority.

Note that SETUP transactions are always either accepted or ignored.
For endpoints that accept SETUP transactions, a SETUP packet will clear the STALL flag on endpoints for both the IN and OUT directions.

### in_stall . endpoint_1
If this bit is set then an IN transaction to this endpoint will elicit a STALL handshake, when a non-isochronous endpoint is enabled.
If the configuration has both STALL and NAK enabled, the STALL handshake will take priority.

Note that SETUP transactions are always either accepted or ignored.
For endpoints that accept SETUP transactions, a SETUP packet will clear the STALL flag on endpoints for both the IN and OUT directions.

### in_stall . endpoint_0
If this bit is set then an IN transaction to this endpoint will elicit a STALL handshake, when a non-isochronous endpoint is enabled.
If the configuration has both STALL and NAK enabled, the STALL handshake will take priority.

Note that SETUP transactions are always either accepted or ignored.
For endpoints that accept SETUP transactions, a SETUP packet will clear the STALL flag on endpoints for both the IN and OUT directions.

## configin
Configure IN Transaction
- Reset default: `0x0`
- Reset mask: `0xe0007f1f`

### Instances

| Name        | Offset   |
|:------------|:---------|
| configin_0  | 0x44     |
| configin_1  | 0x48     |
| configin_2  | 0x4c     |
| configin_3  | 0x50     |
| configin_4  | 0x54     |
| configin_5  | 0x58     |
| configin_6  | 0x5c     |
| configin_7  | 0x60     |
| configin_8  | 0x64     |
| configin_9  | 0x68     |
| configin_10 | 0x6c     |
| configin_11 | 0x70     |


### Fields

```wavejson
{"reg": [{"name": "buffer", "bits": 5, "attr": ["rw"], "rotate": 0}, {"bits": 3}, {"name": "size", "bits": 7, "attr": ["rw"], "rotate": 0}, {"bits": 14}, {"name": "sending", "bits": 1, "attr": ["rw1c"], "rotate": -90}, {"name": "pend", "bits": 1, "attr": ["rw1c"], "rotate": -90}, {"name": "rdy", "bits": 1, "attr": ["rw"], "rotate": -90}], "config": {"lanes": 1, "fontsize": 10, "vspace": 90}}
```

|  Bits  |  Type  |  Reset  | Name                          |
|:------:|:------:|:-------:|:------------------------------|
|   31   |   rw   |   0x0   | [rdy](#configin--rdy)         |
|   30   |  rw1c  |   0x0   | [pend](#configin--pend)       |
|   29   |  rw1c  |   0x0   | [sending](#configin--sending) |
| 28:15  |        |         | Reserved                      |
|  14:8  |   rw   |   0x0   | [size](#configin--size)       |
|  7:5   |        |         | Reserved                      |
|  4:0   |   rw   |   0x0   | [buffer](#configin--buffer)   |

### configin . rdy
This bit should be set to indicate the buffer is ready for sending.
It will be cleared when the ACK is received indicating the host has accepted the data.

This bit will also be cleared if an enabled SETUP transaction is received on the endpoint.
This allows use of the IN channel for transfer of SETUP information.
The original buffer must be resubmitted after the SETUP sequence is complete.
A link reset also clears the bit.
In either of the cases where the hardware cancels the transaction it will also set the pend bit.

### configin . pend
This bit indicates a pending transaction was canceled by the hardware.

The bit is set when the rdy bit is cleared by hardware because of a
SETUP packet being received or a link reset being detected.

The bit remains set until cleared by being written with a 1.

### configin . sending
This bit indicates that the buffer is in the process of being collected by the
host. It becomes set upon the first attempt by the host to collect a buffer from
this endpoint when the rdy bit was set.

It is cleared when the packet has been collected successfully or the pending
transaction has been canceled by the hardware through detection of a
link reset or receipt of a SETUP packet.

### configin . size
The number of bytes to send from the buffer.

If this is 0 then a CRC only packet is sent.

If this is greater than 64 then 64 bytes are sent.

### configin . buffer
The buffer ID containing the data to send when an IN transaction is received on the endpoint.

## out_iso
OUT Endpoint isochronous setting
- Offset: `0x74`
- Reset default: `0x0`
- Reset mask: `0xfff`

### Fields

```wavejson
{"reg": [{"name": "iso_0", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "iso_1", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "iso_2", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "iso_3", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "iso_4", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "iso_5", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "iso_6", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "iso_7", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "iso_8", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "iso_9", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "iso_10", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "iso_11", "bits": 1, "attr": ["rw"], "rotate": -90}, {"bits": 20}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name                       |
|:------:|:------:|:-------:|:---------------------------|
| 31:12  |        |         | Reserved                   |
|   11   |   rw   |   0x0   | [iso_11](#out_iso--iso_11) |
|   10   |   rw   |   0x0   | [iso_10](#out_iso--iso_10) |
|   9    |   rw   |   0x0   | [iso_9](#out_iso--iso_9)   |
|   8    |   rw   |   0x0   | [iso_8](#out_iso--iso_8)   |
|   7    |   rw   |   0x0   | [iso_7](#out_iso--iso_7)   |
|   6    |   rw   |   0x0   | [iso_6](#out_iso--iso_6)   |
|   5    |   rw   |   0x0   | [iso_5](#out_iso--iso_5)   |
|   4    |   rw   |   0x0   | [iso_4](#out_iso--iso_4)   |
|   3    |   rw   |   0x0   | [iso_3](#out_iso--iso_3)   |
|   2    |   rw   |   0x0   | [iso_2](#out_iso--iso_2)   |
|   1    |   rw   |   0x0   | [iso_1](#out_iso--iso_1)   |
|   0    |   rw   |   0x0   | [iso_0](#out_iso--iso_0)   |

### out_iso . iso_11
If this bit is set then the endpoint will be treated as an isochronous endpoint.
No handshake packet will be sent for an OUT transaction.
Note that if a rxenable_setup is set for this endpoint's number, this bit will not take effect.
Control endpoint configuration trumps isochronous endpoint configuration.

### out_iso . iso_10
If this bit is set then the endpoint will be treated as an isochronous endpoint.
No handshake packet will be sent for an OUT transaction.
Note that if a rxenable_setup is set for this endpoint's number, this bit will not take effect.
Control endpoint configuration trumps isochronous endpoint configuration.

### out_iso . iso_9
If this bit is set then the endpoint will be treated as an isochronous endpoint.
No handshake packet will be sent for an OUT transaction.
Note that if a rxenable_setup is set for this endpoint's number, this bit will not take effect.
Control endpoint configuration trumps isochronous endpoint configuration.

### out_iso . iso_8
If this bit is set then the endpoint will be treated as an isochronous endpoint.
No handshake packet will be sent for an OUT transaction.
Note that if a rxenable_setup is set for this endpoint's number, this bit will not take effect.
Control endpoint configuration trumps isochronous endpoint configuration.

### out_iso . iso_7
If this bit is set then the endpoint will be treated as an isochronous endpoint.
No handshake packet will be sent for an OUT transaction.
Note that if a rxenable_setup is set for this endpoint's number, this bit will not take effect.
Control endpoint configuration trumps isochronous endpoint configuration.

### out_iso . iso_6
If this bit is set then the endpoint will be treated as an isochronous endpoint.
No handshake packet will be sent for an OUT transaction.
Note that if a rxenable_setup is set for this endpoint's number, this bit will not take effect.
Control endpoint configuration trumps isochronous endpoint configuration.

### out_iso . iso_5
If this bit is set then the endpoint will be treated as an isochronous endpoint.
No handshake packet will be sent for an OUT transaction.
Note that if a rxenable_setup is set for this endpoint's number, this bit will not take effect.
Control endpoint configuration trumps isochronous endpoint configuration.

### out_iso . iso_4
If this bit is set then the endpoint will be treated as an isochronous endpoint.
No handshake packet will be sent for an OUT transaction.
Note that if a rxenable_setup is set for this endpoint's number, this bit will not take effect.
Control endpoint configuration trumps isochronous endpoint configuration.

### out_iso . iso_3
If this bit is set then the endpoint will be treated as an isochronous endpoint.
No handshake packet will be sent for an OUT transaction.
Note that if a rxenable_setup is set for this endpoint's number, this bit will not take effect.
Control endpoint configuration trumps isochronous endpoint configuration.

### out_iso . iso_2
If this bit is set then the endpoint will be treated as an isochronous endpoint.
No handshake packet will be sent for an OUT transaction.
Note that if a rxenable_setup is set for this endpoint's number, this bit will not take effect.
Control endpoint configuration trumps isochronous endpoint configuration.

### out_iso . iso_1
If this bit is set then the endpoint will be treated as an isochronous endpoint.
No handshake packet will be sent for an OUT transaction.
Note that if a rxenable_setup is set for this endpoint's number, this bit will not take effect.
Control endpoint configuration trumps isochronous endpoint configuration.

### out_iso . iso_0
If this bit is set then the endpoint will be treated as an isochronous endpoint.
No handshake packet will be sent for an OUT transaction.
Note that if a rxenable_setup is set for this endpoint's number, this bit will not take effect.
Control endpoint configuration trumps isochronous endpoint configuration.

## in_iso
IN Endpoint isochronous setting
- Offset: `0x78`
- Reset default: `0x0`
- Reset mask: `0xfff`

### Fields

```wavejson
{"reg": [{"name": "iso_0", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "iso_1", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "iso_2", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "iso_3", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "iso_4", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "iso_5", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "iso_6", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "iso_7", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "iso_8", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "iso_9", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "iso_10", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "iso_11", "bits": 1, "attr": ["rw"], "rotate": -90}, {"bits": 20}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name                      |
|:------:|:------:|:-------:|:--------------------------|
| 31:12  |        |         | Reserved                  |
|   11   |   rw   |   0x0   | [iso_11](#in_iso--iso_11) |
|   10   |   rw   |   0x0   | [iso_10](#in_iso--iso_10) |
|   9    |   rw   |   0x0   | [iso_9](#in_iso--iso_9)   |
|   8    |   rw   |   0x0   | [iso_8](#in_iso--iso_8)   |
|   7    |   rw   |   0x0   | [iso_7](#in_iso--iso_7)   |
|   6    |   rw   |   0x0   | [iso_6](#in_iso--iso_6)   |
|   5    |   rw   |   0x0   | [iso_5](#in_iso--iso_5)   |
|   4    |   rw   |   0x0   | [iso_4](#in_iso--iso_4)   |
|   3    |   rw   |   0x0   | [iso_3](#in_iso--iso_3)   |
|   2    |   rw   |   0x0   | [iso_2](#in_iso--iso_2)   |
|   1    |   rw   |   0x0   | [iso_1](#in_iso--iso_1)   |
|   0    |   rw   |   0x0   | [iso_0](#in_iso--iso_0)   |

### in_iso . iso_11
If this bit is set then the endpoint will be treated as an isochronous endpoint.
No handshake packet will be expected for an IN transaction.
Note that if a rxenable_setup is set for this endpoint's number, this bit will not take effect.
Control endpoint configuration trumps isochronous endpoint configuration.

### in_iso . iso_10
If this bit is set then the endpoint will be treated as an isochronous endpoint.
No handshake packet will be expected for an IN transaction.
Note that if a rxenable_setup is set for this endpoint's number, this bit will not take effect.
Control endpoint configuration trumps isochronous endpoint configuration.

### in_iso . iso_9
If this bit is set then the endpoint will be treated as an isochronous endpoint.
No handshake packet will be expected for an IN transaction.
Note that if a rxenable_setup is set for this endpoint's number, this bit will not take effect.
Control endpoint configuration trumps isochronous endpoint configuration.

### in_iso . iso_8
If this bit is set then the endpoint will be treated as an isochronous endpoint.
No handshake packet will be expected for an IN transaction.
Note that if a rxenable_setup is set for this endpoint's number, this bit will not take effect.
Control endpoint configuration trumps isochronous endpoint configuration.

### in_iso . iso_7
If this bit is set then the endpoint will be treated as an isochronous endpoint.
No handshake packet will be expected for an IN transaction.
Note that if a rxenable_setup is set for this endpoint's number, this bit will not take effect.
Control endpoint configuration trumps isochronous endpoint configuration.

### in_iso . iso_6
If this bit is set then the endpoint will be treated as an isochronous endpoint.
No handshake packet will be expected for an IN transaction.
Note that if a rxenable_setup is set for this endpoint's number, this bit will not take effect.
Control endpoint configuration trumps isochronous endpoint configuration.

### in_iso . iso_5
If this bit is set then the endpoint will be treated as an isochronous endpoint.
No handshake packet will be expected for an IN transaction.
Note that if a rxenable_setup is set for this endpoint's number, this bit will not take effect.
Control endpoint configuration trumps isochronous endpoint configuration.

### in_iso . iso_4
If this bit is set then the endpoint will be treated as an isochronous endpoint.
No handshake packet will be expected for an IN transaction.
Note that if a rxenable_setup is set for this endpoint's number, this bit will not take effect.
Control endpoint configuration trumps isochronous endpoint configuration.

### in_iso . iso_3
If this bit is set then the endpoint will be treated as an isochronous endpoint.
No handshake packet will be expected for an IN transaction.
Note that if a rxenable_setup is set for this endpoint's number, this bit will not take effect.
Control endpoint configuration trumps isochronous endpoint configuration.

### in_iso . iso_2
If this bit is set then the endpoint will be treated as an isochronous endpoint.
No handshake packet will be expected for an IN transaction.
Note that if a rxenable_setup is set for this endpoint's number, this bit will not take effect.
Control endpoint configuration trumps isochronous endpoint configuration.

### in_iso . iso_1
If this bit is set then the endpoint will be treated as an isochronous endpoint.
No handshake packet will be expected for an IN transaction.
Note that if a rxenable_setup is set for this endpoint's number, this bit will not take effect.
Control endpoint configuration trumps isochronous endpoint configuration.

### in_iso . iso_0
If this bit is set then the endpoint will be treated as an isochronous endpoint.
No handshake packet will be expected for an IN transaction.
Note that if a rxenable_setup is set for this endpoint's number, this bit will not take effect.
Control endpoint configuration trumps isochronous endpoint configuration.

## out_data_toggle
OUT Endpoints Data Toggles
- Offset: `0x7c`
- Reset default: `0x0`
- Reset mask: `0xfff0fff`

### Fields

```wavejson
{"reg": [{"name": "status", "bits": 12, "attr": ["rw"], "rotate": 0}, {"bits": 4}, {"name": "mask", "bits": 12, "attr": ["rw"], "rotate": 0}, {"bits": 4}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name   | Description                                                                                                                                                                                           |
|:------:|:------:|:-------:|:-------|:------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------|
| 31:28  |        |         |        | Reserved                                                                                                                                                                                              |
| 27:16  |   rw   |    x    | mask   | Reads as zero. When writing, a set bit will cause the Data Toggle flag of the corresponding OUT endpoint to be updated. A clear bit will leave the flag for the corresponding endpoint unchanged.     |
| 15:12  |        |         |        | Reserved                                                                                                                                                                                              |
|  11:0  |   rw   |    x    | status | Reading returns the current state of the OUT endpoint Data Toggle flags. Writing sets the Data Toggle flag for each endpoint if the corresponding mask bit in the upper half of this register is set. |

## in_data_toggle
IN Endpoints Data Toggles
- Offset: `0x80`
- Reset default: `0x0`
- Reset mask: `0xfff0fff`

### Fields

```wavejson
{"reg": [{"name": "status", "bits": 12, "attr": ["rw"], "rotate": 0}, {"bits": 4}, {"name": "mask", "bits": 12, "attr": ["rw"], "rotate": 0}, {"bits": 4}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name   | Description                                                                                                                                                                                          |
|:------:|:------:|:-------:|:-------|:-----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------|
| 31:28  |        |         |        | Reserved                                                                                                                                                                                             |
| 27:16  |   rw   |    x    | mask   | Reads as zero. When writing, a set bit will cause the Data Toggle flag of the corresponding IN endpoint to be updated. A clear bit will leave the flag for the corresponding endpoint unchanged.     |
| 15:12  |        |         |        | Reserved                                                                                                                                                                                             |
|  11:0  |   rw   |    x    | status | Reading returns the current state of the IN endpoint Data Toggle flags. Writing sets the Data Toggle flag for each endpoint if the corresponding mask bit in the upper half of this register is set. |

## phy_pins_sense
USB PHY pins sense.
This register can be used to read out the state of the USB device inputs and outputs from software.
This is designed to be used for debugging purposes or during chip testing.
- Offset: `0x84`
- Reset default: `0x0`
- Reset mask: `0x11f07`

### Fields

```wavejson
{"reg": [{"name": "rx_dp_i", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "rx_dn_i", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "rx_d_i", "bits": 1, "attr": ["ro"], "rotate": -90}, {"bits": 5}, {"name": "tx_dp_o", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "tx_dn_o", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "tx_d_o", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "tx_se0_o", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "tx_oe_o", "bits": 1, "attr": ["ro"], "rotate": -90}, {"bits": 3}, {"name": "pwr_sense", "bits": 1, "attr": ["ro"], "rotate": -90}, {"bits": 15}], "config": {"lanes": 1, "fontsize": 10, "vspace": 110}}
```

|  Bits  |  Type  |  Reset  | Name      | Description                                                          |
|:------:|:------:|:-------:|:----------|:---------------------------------------------------------------------|
| 31:17  |        |         |           | Reserved                                                             |
|   16   |   ro   |    x    | pwr_sense | USB power sense signal.                                              |
| 15:13  |        |         |           | Reserved                                                             |
|   12   |   ro   |    x    | tx_oe_o   | USB OE output (readback).                                            |
|   11   |   ro   |    x    | tx_se0_o  | USB single-ended zero output (readback).                             |
|   10   |   ro   |    x    | tx_d_o    | USB transmit data value (readback).                                  |
|   9    |   ro   |    x    | tx_dn_o   | USB transmit D- output (readback).                                   |
|   8    |   ro   |    x    | tx_dp_o   | USB transmit D+ output (readback).                                   |
|  7:3   |        |         |           | Reserved                                                             |
|   2    |   ro   |    x    | rx_d_i    | USB data input from an external differential receiver, if available. |
|   1    |   ro   |    x    | rx_dn_i   | USB D- input.                                                        |
|   0    |   ro   |    x    | rx_dp_i   | USB D+ input.                                                        |

## phy_pins_drive
USB PHY pins drive.
This register can be used to control the USB device inputs and outputs from software.
This is designed to be used for debugging purposes or during chip testing.
- Offset: `0x88`
- Reset default: `0x0`
- Reset mask: `0x100ff`

### Fields

```wavejson
{"reg": [{"name": "dp_o", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "dn_o", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "d_o", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "se0_o", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "oe_o", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "rx_enable_o", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "dp_pullup_en_o", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "dn_pullup_en_o", "bits": 1, "attr": ["rw"], "rotate": -90}, {"bits": 8}, {"name": "en", "bits": 1, "attr": ["rw"], "rotate": -90}, {"bits": 15}], "config": {"lanes": 1, "fontsize": 10, "vspace": 160}}
```

|  Bits  |  Type  |  Reset  | Name           | Description                                                                                    |
|:------:|:------:|:-------:|:---------------|:-----------------------------------------------------------------------------------------------|
| 31:17  |        |         |                | Reserved                                                                                       |
|   16   |   rw   |   0x0   | en             | 0: Outputs are controlled by the hardware block. 1: Outputs are controlled with this register. |
|  15:8  |        |         |                | Reserved                                                                                       |
|   7    |   rw   |   0x0   | dn_pullup_en_o | USB D- pullup enable output.                                                                   |
|   6    |   rw   |   0x0   | dp_pullup_en_o | USB D+ pullup enable output.                                                                   |
|   5    |   rw   |   0x0   | rx_enable_o    | Enable differential receiver.                                                                  |
|   4    |   rw   |   0x0   | oe_o           | USB OE output.                                                                                 |
|   3    |   rw   |   0x0   | se0_o          | USB single-ended zero output.                                                                  |
|   2    |   rw   |   0x0   | d_o            | USB transmit data output, encoding K and J when se0_o is 0.                                    |
|   1    |   rw   |   0x0   | dn_o           | USB transmit D- output, used with dp_o.                                                        |
|   0    |   rw   |   0x0   | dp_o           | USB transmit D+ output, used with dn_o.                                                        |

## phy_config
USB PHY Configuration
- Offset: `0x8c`
- Reset default: `0x4`
- Reset mask: `0xe7`

### Fields

```wavejson
{"reg": [{"name": "use_diff_rcvr", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "tx_use_d_se0", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "eop_single_bit", "bits": 1, "attr": ["rw"], "rotate": -90}, {"bits": 2}, {"name": "pinflip", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "usb_ref_disable", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "tx_osc_test_mode", "bits": 1, "attr": ["rw"], "rotate": -90}, {"bits": 24}], "config": {"lanes": 1, "fontsize": 10, "vspace": 180}}
```

|  Bits  |  Type  |  Reset  | Name                                              |
|:------:|:------:|:-------:|:--------------------------------------------------|
|  31:8  |        |         | Reserved                                          |
|   7    |   rw   |   0x0   | [tx_osc_test_mode](#phy_config--tx_osc_test_mode) |
|   6    |   rw   |   0x0   | [usb_ref_disable](#phy_config--usb_ref_disable)   |
|   5    |   rw   |   0x0   | [pinflip](#phy_config--pinflip)                   |
|  4:3   |        |         | Reserved                                          |
|   2    |   rw   |   0x1   | [eop_single_bit](#phy_config--eop_single_bit)     |
|   1    |   rw   |   0x0   | [tx_use_d_se0](#phy_config--tx_use_d_se0)         |
|   0    |   rw   |   0x0   | [use_diff_rcvr](#phy_config--use_diff_rcvr)       |

### phy_config . tx_osc_test_mode
Disable (0) or enable (1) oscillator test mode.
If enabled, the device constantly transmits a J/K pattern, which is useful for testing the USB clock.
Note that while in oscillator test mode, the device no longer receives SOFs and consequently does not generate the reference signal for clock synchronization.
The clock might drift off.


### phy_config . usb_ref_disable
0: Enable reference signal generation for clock synchronization, 1: disable it by forcing the associated signals to zero.


### phy_config . pinflip
Flip the D+/D- pins.
Particularly useful if D+/D- are mapped to SBU1/SBU2 pins of USB-C.


### phy_config . eop_single_bit
Recognize a single SE0 bit as an end of packet, otherwise two successive bits are required.

### phy_config . tx_use_d_se0
If 1, select the d and se0 TX interface.
If 0, select the dp and dn TX interface.
This directly controls the output pin of the same name.
It is intended to be used to enable the use of a variety of external transceivers, to select an encoding that matches the transceiver.

### phy_config . use_diff_rcvr
Detect received K and J symbols from the usb_rx_d signal, which must be driven from an external differential receiver.
If 1, make use of the usb_rx_d input.
If 0, the usb_rx_d input is ignored and the usb_rx_dp and usb_rx_dn pair are used to detect K and J (useful for some environments, but will be unlikely to pass full USB compliance).
Regardless of the state of this field usb_rx_dp and usb_rx_dn are always used to detect SE0.
This bit also feeds the rx_enable pin, activating the receiver when the device is not suspended.

## wake_control
USB wake module control for suspend / resume
- Offset: `0x90`
- Reset default: `0x0`
- Reset mask: `0x3`

### Fields

```wavejson
{"reg": [{"name": "suspend_req", "bits": 1, "attr": ["wo"], "rotate": -90}, {"name": "wake_ack", "bits": 1, "attr": ["wo"], "rotate": -90}, {"bits": 30}], "config": {"lanes": 1, "fontsize": 10, "vspace": 130}}
```

|  Bits  |  Type  |  Reset  | Name                                      |
|:------:|:------:|:-------:|:------------------------------------------|
|  31:2  |        |         | Reserved                                  |
|   1    |   wo   |   0x0   | [wake_ack](#wake_control--wake_ack)       |
|   0    |   wo   |   0x0   | [suspend_req](#wake_control--suspend_req) |

### wake_control . wake_ack
Wake acknowledgement.

Signal to the wake detection module that it may release control of the pull-ups back to the main block and return to an inactive state.
The release back to normal state may not happen immediately.
The status can be confirmed via wake_events.module_active.

Note that this bit can also be used without powering down, such as when usbdev detects resume signaling before transitions to low power states have begun.

### wake_control . suspend_req
Suspend request to the wake detection module.

Trigger the wake detection module to begin monitoring for wake-from-suspend events.
When written with a 1, the wake detection module will activate.
Activation may not happen immediately, and its status can be verified by checking wake_events.module_active.

## wake_events
USB wake module events and debug
- Offset: `0x94`
- Reset default: `0x0`
- Reset mask: `0x701`

### Fields

```wavejson
{"reg": [{"name": "module_active", "bits": 1, "attr": ["ro"], "rotate": -90}, {"bits": 7}, {"name": "disconnected", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "bus_reset", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "bus_not_idle", "bits": 1, "attr": ["ro"], "rotate": -90}, {"bits": 21}], "config": {"lanes": 1, "fontsize": 10, "vspace": 150}}
```

|  Bits  |  Type  |  Reset  | Name          | Description                                                                    |
|:------:|:------:|:-------:|:--------------|:-------------------------------------------------------------------------------|
| 31:11  |        |         |               | Reserved                                                                       |
|   10   |   ro   |   0x0   | bus_not_idle  | USB aon wake module detected a non-idle bus while monitoring events.           |
|   9    |   ro   |   0x0   | bus_reset     | USB aon wake module detected a bus reset while monitoring events.              |
|   8    |   ro   |   0x0   | disconnected  | USB aon wake module detected VBUS was interrupted while monitoring events.     |
|  7:1   |        |         |               | Reserved                                                                       |
|   0    |   ro   |   0x0   | module_active | USB aon wake module is active, monitoring events and controlling the pull-ups. |

## fifo_ctrl
FIFO control register
- Offset: `0x98`
- Reset default: `0x0`
- Reset mask: `0x7`

### Fields

```wavejson
{"reg": [{"name": "avout_rst", "bits": 1, "attr": ["wo"], "rotate": -90}, {"name": "avsetup_rst", "bits": 1, "attr": ["wo"], "rotate": -90}, {"name": "rx_rst", "bits": 1, "attr": ["wo"], "rotate": -90}, {"bits": 29}], "config": {"lanes": 1, "fontsize": 10, "vspace": 130}}
```

|  Bits  |  Type  |  Reset  | Name        | Description                                                                                                                |
|:------:|:------:|:-------:|:------------|:---------------------------------------------------------------------------------------------------------------------------|
|  31:3  |        |         |             | Reserved                                                                                                                   |
|   2    |   wo   |   0x0   | rx_rst      | Software reset the of Rx Buffer FIFO. This must be used only when the USB device is not connected to the USB.              |
|   1    |   wo   |   0x0   | avsetup_rst | Software reset of the Available SETUP Buffer FIFO. This must be used only when the USB device is not connected to the USB. |
|   0    |   wo   |   0x0   | avout_rst   | Software reset of the Available OUT Buffer FIFO. This must be used only when the USB device is not connected to the USB.   |

## count_out
Counter for OUT side USB events.
- Offset: `0x9c`
- Reset default: `0x0`
- Reset mask: `0x8ffff0ff`

### Fields

```wavejson
{"reg": [{"name": "count", "bits": 8, "attr": ["ro"], "rotate": 0}, {"bits": 4}, {"name": "datatog_out", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "drop_rx", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "drop_avout", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "ign_avsetup", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "endpoints", "bits": 12, "attr": ["rw"], "rotate": 0}, {"bits": 3}, {"name": "rst", "bits": 1, "attr": ["wo"], "rotate": -90}], "config": {"lanes": 1, "fontsize": 10, "vspace": 130}}
```

|  Bits  |  Type  |  Reset  | Name                                   |
|:------:|:------:|:-------:|:---------------------------------------|
|   31   |   wo   |   0x0   | [rst](#count_out--rst)                 |
| 30:28  |        |         | Reserved                               |
| 27:16  |   rw   |   0x0   | [endpoints](#count_out--endpoints)     |
|   15   |   rw   |   0x0   | [ign_avsetup](#count_out--ign_avsetup) |
|   14   |   rw   |   0x0   | [drop_avout](#count_out--drop_avout)   |
|   13   |   rw   |   0x0   | [drop_rx](#count_out--drop_rx)         |
|   12   |   rw   |   0x0   | [datatog_out](#count_out--datatog_out) |
|  11:8  |        |         | Reserved                               |
|  7:0   |   ro   |   0x0   | [count](#count_out--count)             |

### count_out . rst
Write 1 to reset the counter.

### count_out . endpoints
Set of OUT endpoints for which this counter is enabled.

### count_out . ign_avsetup
Count the SETUP packets that were ignored because there was no buffer in the
Av SETUP FIFO.

### count_out . drop_avout
Count the OUT packets that could not be accepted because there was no buffer in the
Av OUT FIFO. Non-Isochronous OUT packets have been NAKed.
Isochronous OUT packets were ignored.

### count_out . drop_rx
Count the SETUP/OUT packets ignored, dropped or NAKed because the RX FIFO was full.
SETUP packets have been ignored, Isochronous OUT packets have been dropped, and
non-Isochronous OUT packets have been NAKed.

### count_out . datatog_out
Count the OUT transactions for which the USB device acknowledged the OUT packet
and dropped it internally, which is the correct response to a packet transmitted
with an incorrect Data Toggle.

The expectation is that this packet is a retry of the previous packet transmission
and that the handshake response was not received intact by the USB host, indicating
unreliable communications.

Other causes of Data Toggle synchronization failure may result in data loss.

### count_out . count
Number of events counted.

## count_in
Counter for IN side USB events.
- Offset: `0xa0`
- Reset default: `0x0`
- Reset mask: `0x8fffe0ff`

### Fields

```wavejson
{"reg": [{"name": "count", "bits": 8, "attr": ["ro"], "rotate": 0}, {"bits": 5}, {"name": "nodata", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "nak", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "timeout", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "endpoints", "bits": 12, "attr": ["rw"], "rotate": 0}, {"bits": 3}, {"name": "rst", "bits": 1, "attr": ["wo"], "rotate": -90}], "config": {"lanes": 1, "fontsize": 10, "vspace": 90}}
```

|  Bits  |  Type  |  Reset  | Name                              |
|:------:|:------:|:-------:|:----------------------------------|
|   31   |   wo   |   0x0   | [rst](#count_in--rst)             |
| 30:28  |        |         | Reserved                          |
| 27:16  |   rw   |   0x0   | [endpoints](#count_in--endpoints) |
|   15   |   rw   |   0x0   | [timeout](#count_in--timeout)     |
|   14   |   rw   |   0x0   | [nak](#count_in--nak)             |
|   13   |   rw   |   0x0   | [nodata](#count_in--nodata)       |
|  12:8  |        |         | Reserved                          |
|  7:0   |   ro   |   0x0   | [count](#count_in--count)         |

### count_in . rst
Write 1 to reset the counter.

### count_in . endpoints
Set of endpoints for which this counter is enabled.

### count_in . timeout
Count the IN transactions for which the USB host did not respond with a handshake,
and the transactions timed out. This indicates that the host did not receive it
and decode it as a valid packet, suggesting that communication is unreliable.

Isochronous IN transactions are excluded from this count because there is no
handshake response to Isochronous packet transfers.

### count_in . nak
Count the IN transactions rejected by the host responding with a NAK handshake.

### count_in . nodata
Count the IN transactions that were attempted when there was no packet available
in the corresponding 'configin' register(s). This is not necessarily an error
condition, and the counter primarily offers some visibility into when the IN
traffic is underusing the available bus bandwidth.
It is of particular utility to Isochronous IN endpoints.

### count_in . count
Number of events counted.

## count_nodata_in
Count of IN transactions for which no packet data was available.

This secondary register allows some partitioning of endpoints among the two
counters, for more targeted measurement, eg. endpoints may be grouped according to
the expected bandwidth usage, or Isochronous vs. non-Isochronous transfers.
- Offset: `0xa4`
- Reset default: `0x0`
- Reset mask: `0x8fff00ff`

### Fields

```wavejson
{"reg": [{"name": "count", "bits": 8, "attr": ["ro"], "rotate": 0}, {"bits": 8}, {"name": "endpoints", "bits": 12, "attr": ["rw"], "rotate": 0}, {"bits": 3}, {"name": "rst", "bits": 1, "attr": ["wo"], "rotate": -90}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name      | Description                                                                                                                   |
|:------:|:------:|:-------:|:----------|:------------------------------------------------------------------------------------------------------------------------------|
|   31   |   wo   |   0x0   | rst       | Write 1 to reset the counter.                                                                                                 |
| 30:28  |        |         |           | Reserved                                                                                                                      |
| 27:16  |   rw   |   0x0   | endpoints | Set of endpoints for which this counter is enabled.                                                                           |
|  15:8  |        |         |           | Reserved                                                                                                                      |
|  7:0   |   ro   |   0x0   | count     | Number of IN transactions that were attempted when there was no packet available in the corresponding 'configin' register(s). |

## count_errors
Count of error conditions detected on token packets from the host.
- Offset: `0xa8`
- Reset default: `0x0`
- Reset mask: `0xf80000ff`

### Fields

```wavejson
{"reg": [{"name": "count", "bits": 8, "attr": ["ro"], "rotate": 0}, {"bits": 19}, {"name": "pid_invalid", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "bitstuff", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "crc16", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "crc5", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "rst", "bits": 1, "attr": ["wo"], "rotate": -90}], "config": {"lanes": 1, "fontsize": 10, "vspace": 130}}
```

|  Bits  |  Type  |  Reset  | Name        | Description                                                                                                                                                                                                                             |
|:------:|:------:|:-------:|:------------|:----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------|
|   31   |   wo   |   0x0   | rst         | Write 1 to reset the counter.                                                                                                                                                                                                           |
|   30   |   rw   |   0x0   | crc5        | Count CRC5 errors detected on token packets sent by the host. CRC5 errors on token packets received from the host indicate very unreliable communication and possibly a substantial frequency mismatch between the host and the device. |
|   29   |   rw   |   0x0   | crc16       | Count SETUP/OUT DATA packets that were ignored, dropped or NAKed because a CRC16 error was detected.                                                                                                                                    |
|   28   |   rw   |   0x0   | bitstuff    | Number of SETUP/OUT packets that were ignored, dropped or NAKed because a Bit Stuffing error was detected.                                                                                                                              |
|   27   |   rw   |   0x0   | pid_invalid | Number of Invalid PIDs detected on packets from the host. Invalid PIDs may indicate very unreliable communication and/or a substantial frequency mismatch between the host and the device.                                              |
|  26:8  |        |         |             | Reserved                                                                                                                                                                                                                                |
|  7:0   |   ro   |   0x0   | count       | Number of events counted.                                                                                                                                                                                                               |

## buffer
2 KiB packet buffer. Divided into thirty two 64-byte buffers.

The packet buffer is used for sending and receiving packets.

- Word Aligned Offset Range: `0x800`to`0xffc`
- Size (words): `512`
- Access: `rw`
- Byte writes are *not* supported.


<!-- END CMDGEN -->
