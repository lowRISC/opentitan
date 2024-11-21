# Hardware Interfaces

<!-- BEGIN CMDGEN util/regtool.py --interfaces ./hw/top_darjeeling/ip_autogen/pinmux/data/pinmux.hjson -->
Referring to the [Comportable guideline for peripheral device functionality](https://opentitan.org/book/doc/contributing/hw/comportability), the module **`pinmux`** has the following hardware interfaces defined
- Primary Clock: **`clk_i`**
- Other Clocks: **`clk_aon_i`**
- Bus Device Interfaces (TL-UL): **`tl`**
- Bus Host Interfaces (TL-UL): *none*
- Peripheral Pins for Chip IO: *none*
- Interrupts: *none*

## [Inter-Module Signals](https://opentitan.org/book/doc/contributing/hw/comportability/index.html#inter-signal-handling)

| Port Name    | Package::Struct   | Type    | Act   |   Width | Description                                                                           |
|:-------------|:------------------|:--------|:------|--------:|:--------------------------------------------------------------------------------------|
| sleep_en     | logic             | uni     | rcv   |       1 | Level signal that is asserted when the power manager enters sleep.                    |
| pin_wkup_req | logic             | uni     | req   |       1 | Wakeup request from wakeup detectors, to the power manager, running on the AON clock. |
| tl           | tlul_pkg::tl      | req_rsp | rsp   |       1 |                                                                                       |

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
