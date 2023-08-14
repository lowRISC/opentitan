# Hardware Interfaces

<!-- BEGIN CMDGEN util/regtool.py --interfaces ./hw/top_earlgrey/ip/pinmux/data/autogen/pinmux.hjson -->
Referring to the [Comportable guideline for peripheral device functionality](https://opentitan.org/book/doc/contributing/hw/comportability), the module **`pinmux`** has the following hardware interfaces defined
- Primary Clock: **`clk_i`**
- Other Clocks: **`clk_aon_i`**
- Bus Device Interfaces (TL-UL): **`tl`**
- Bus Host Interfaces (TL-UL): *none*
- Peripheral Pins for Chip IO: *none*
- Interrupts: *none*

## [Inter-Module Signals](https://opentitan.org/book/doc/contributing/hw/comportability/index.html#inter-signal-handling)

| Port Name                 | Package::Struct                | Type    | Act   |   Width | Description                                                                                                                                                                                                                                                                                                                                                                                          |
|:--------------------------|:-------------------------------|:--------|:------|--------:|:-----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------|
| lc_hw_debug_en            | lc_ctrl_pkg::lc_tx             | uni     | rcv   |       1 | Debug enable qualifier coming from life cycle controller, used for HW strap qualification.                                                                                                                                                                                                                                                                                                           |
| lc_dft_en                 | lc_ctrl_pkg::lc_tx             | uni     | rcv   |       1 | Test enable qualifier coming from life cycle controller, used for HW strap qualification.                                                                                                                                                                                                                                                                                                            |
| lc_escalate_en            | lc_ctrl_pkg::lc_tx             | uni     | rcv   |       1 | Escalation enable signal coming from life cycle controller, used for invalidating the latched lc_hw_debug_en state inside the strap sampling logic.                                                                                                                                                                                                                                                  |
| lc_check_byp_en           | lc_ctrl_pkg::lc_tx             | uni     | rcv   |       1 | Check bypass enable signal coming from life cycle controller, used for invalidating the latched lc_hw_debug_en state inside the strap sampling logic. This signal is asserted whenever the life cycle controller performs a life cycle transition. Its main use is to skip any background checks inside the life cycle partition of the OTP controller while a life cycle transition is in progress. |
| pinmux_hw_debug_en        | lc_ctrl_pkg::lc_tx             | uni     | req   |       1 | This is the latched version of lc_hw_debug_en_i. We use it exclusively to gate the JTAG signals and TAP side of the RV_DM so that RV_DM can remain live during an NDM reset cycle.                                                                                                                                                                                                                   |
| lc_jtag                   | jtag_pkg::jtag                 | req_rsp | req   |       1 | Qualified JTAG signals for life cycle controller TAP.                                                                                                                                                                                                                                                                                                                                                |
| rv_jtag                   | jtag_pkg::jtag                 | req_rsp | req   |       1 | Qualified JTAG signals for RISC-V processor TAP.                                                                                                                                                                                                                                                                                                                                                     |
| dft_jtag                  | jtag_pkg::jtag                 | req_rsp | req   |       1 | Qualified JTAG signals for DFT TAP.                                                                                                                                                                                                                                                                                                                                                                  |
| dft_strap_test            | pinmux_pkg::dft_strap_test_req | uni     | req   |       1 | Sampled DFT strap values, going to the DFT TAP.                                                                                                                                                                                                                                                                                                                                                      |
| dft_hold_tap_sel          | logic                          | uni     | rcv   |       1 | TAP selection hold indication, asserted by the DFT TAP during boundary scan.                                                                                                                                                                                                                                                                                                                         |
| sleep_en                  | logic                          | uni     | rcv   |       1 | Level signal that is asserted when the power manager enters sleep.                                                                                                                                                                                                                                                                                                                                   |
| strap_en                  | logic                          | uni     | rcv   |       1 | This signal is pulsed high by the power manager after reset in order to sample the HW straps.                                                                                                                                                                                                                                                                                                        |
| strap_en_override         | logic                          | uni     | rcv   |       1 | This signal transitions from 0 -> 1 by the lc_ctrl manager after volatile RAW_UNLOCK in order to re-sample the HW straps. The signal must stay at 1 until reset. Note that this is only used in test chips when SecVolatileRawUnlockEn = 1. Otherwise this signal is unused.                                                                                                                         |
| pin_wkup_req              | logic                          | uni     | req   |       1 | Wakeup request from wakeup detectors, to the power manager, running on the AON clock.                                                                                                                                                                                                                                                                                                                |
| usbdev_dppullup_en        | logic                          | uni     | rcv   |       1 | Pullup enable signal coming from the USB IP.                                                                                                                                                                                                                                                                                                                                                         |
| usbdev_dnpullup_en        | logic                          | uni     | rcv   |       1 | Pullup enable signal coming from the USB IP.                                                                                                                                                                                                                                                                                                                                                         |
| usb_dppullup_en           | logic                          | uni     | req   |       1 | Pullup enable signal going to USB PHY, needs to be maintained in low-power mode.                                                                                                                                                                                                                                                                                                                     |
| usb_dnpullup_en           | logic                          | uni     | req   |       1 | Pullup enable signal going to USB PHY, needs to be maintained in low-power mode.                                                                                                                                                                                                                                                                                                                     |
| usb_wkup_req              | logic                          | uni     | req   |       1 | Wakeup request from USB wakeup detector, going to the power manager, running on the AON clock.                                                                                                                                                                                                                                                                                                       |
| usbdev_suspend_req        | logic                          | uni     | rcv   |       1 | Indicates whether USB is in suspended state, coming from the USB device.                                                                                                                                                                                                                                                                                                                             |
| usbdev_wake_ack           | logic                          | uni     | rcv   |       1 | Acknowledges the USB wakeup request, coming from the USB device.                                                                                                                                                                                                                                                                                                                                     |
| usbdev_bus_reset          | logic                          | uni     | req   |       1 | Event signal that indicates what happened while monitoring.                                                                                                                                                                                                                                                                                                                                          |
| usbdev_sense_lost         | logic                          | uni     | req   |       1 | Event signal that indicates what happened while monitoring.                                                                                                                                                                                                                                                                                                                                          |
| usbdev_wake_detect_active | logic                          | uni     | req   |       1 | State debug information.                                                                                                                                                                                                                                                                                                                                                                             |
| tl                        | tlul_pkg::tl                   | req_rsp | rsp   |       1 |                                                                                                                                                                                                                                                                                                                                                                                                      |

## Security Alerts

| Alert Name   | Description                                                                       |
|:-------------|:----------------------------------------------------------------------------------|
| fatal_fault  | This fatal alert is triggered when a fatal TL-UL bus integrity fault is detected. |

## Security Countermeasures

| Countermeasure ID    | Description                      |
|:---------------------|:---------------------------------|
| PINMUX.BUS.INTEGRITY | End-to-end bus integrity scheme. |


<!-- END CMDGEN -->

## Parameters

The following table lists the main parameters used throughout the `pinmux` design.
Note that the `pinmux` is generated based on the system configuration, and hence these parameters are placed into a package.
The pinout and `pinmux` mappings are listed under [Pinout and Pinmux Mapping](#pinout-and-pinmux-mapping) for specific top-level configurations.

Parameter      | Description
---------------|---------------
`NPeriphOut`   | Number of peripheral outputs.
`NPeriphIn`    | Number of peripheral input.
`NMioPads`     | Number of muxed bidirectional pads.
`NDioPads`     | Number of dedicated pads.

## Primary IO Signals

The table below lists the primary `pinmux` IO signals to/from the pad ring.
The number of dedicated and muxed IOs is parametric, and hence the signals are stacked in packed arrays.

Signal                                 | Direction | Type                               | Description
---------------------------------------|-----------|------------------------------------|---------------
`periph_to_mio_i[NPeriphOut-1:0]`      | `input`   | packed `logic`                     | Signals from `NPeriphOut` muxed peripheral outputs coming into the `pinmux`.
`periph_to_mio_oe_i[NPeriphOut-1:0]`   | `input`   | packed `logic`                     | Signals from `NPeriphOut` muxed peripheral output enables coming into the `pinmux`.
`mio_to_periph_o[NPeriphIn-1:0]`       | `output`  | packed `logic`                     | Signals to `NPeriphIn` muxed peripherals coming from the `pinmux`.
`periph_to_dio_i[NDioPads-1:0]`        | `input`   | packed `logic`                     | Signals from `NDioPads` dedicated peripheral outputs coming into the `pinmux`.
`periph_to_dio_oe_i[NDioPads-1:0]`     | `input`   | packed `logic`                     | Signals from `NDioPads` dedicated peripheral output enables coming into the `pinmux`.
`dio_to_periph_o[NDioPads-1:0]`        | `output`  | packed `logic`                     | Signals to `NDioPads` dedicated peripherals coming from the `pinmux`.
`mio_attr_o[NMioPads-1:0]`             | `output`  | prim_pad_wrapper_pkg::pad_attr_t   | Packed array containing the pad attributes of all muxed IOs.
`mio_out_o[NMioPads-1:0]`              | `output`  | packed `logic`                     | Signals to `NMioPads` bidirectional muxed pads as output data.
`mio_oe_o[NMioPads-1:0]`               | `output`  | packed `logic`                     | Signals to `NMioPads` bidirectional muxed pads as output enables.
`mio_in_i[NMioPads-1:0]`               | `input`   | packed `logic`                     | Signals from `NMioPads` bidirectional muxed pads as input data.
`dio_attr_o[NDioPads-1:0]`             | `output`  | prim_pad_wrapper_pkg::pad_attr_t   | Packed array containing the pad attributes of all dedicated IOs.
`dio_out_o[NDioPads-1:0]`              | `output`  | packed `logic`                     | Signals to `NDioPads` bidirectional dedicated pads as output data.
`dio_oe_o[NDioPads-1:0]`               | `output`  | packed `logic`                     | Signals to `NDioPads` bidirectional dedicated pads as output enables.
`dio_in_i[NDioPads-1:0]`               | `input`   | packed `logic`                     | Signals from `NDioPads` bidirectional dedicated pads as input data.
