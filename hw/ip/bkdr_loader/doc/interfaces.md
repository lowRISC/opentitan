# Hardware Interfaces

## Parameters

The following table lists the instantiation parameters of the backdoor loader.

Parameter                   | Default               | Top Earlgrey      | Description
----------------------------|-----------------------|-------------------|---------------
`NumBkdrTgts`               | 12                    | 12                | Number of RAM targets supported.
`MaxWordWidthDiv32`         | 8                     | 8                 | Supports up to 256-bit words.

## Signals

<!-- BEGIN CMDGEN util/regtool.py --interfaces ./hw/ip/bkdr_loader/data/bkdr_loader.hjson -->
Referring to the [Comportable guideline for peripheral device functionality](https://opentitan.org/book/doc/contributing/hw/comportability), the module **`bkdr_loader`** has the following hardware interfaces defined
- Primary Clock: **`clk_i`**
- Other Clocks: *none*
- Bus Device Interfaces (TL-UL): **`regs_tl`**
- Bus Host Interfaces (TL-UL): *none*
- Peripheral Pins for Chip IO: *none*
- Interrupts: *none*
- Security Alerts: *none*
- Security Countermeasures: *none*

## [Inter-Module Signals](https://opentitan.org/book/doc/contributing/hw/comportability/index.html#inter-signal-handling)

| Port Name   | Package::Struct   | Type    | Act   |   Width | Description   |
|:------------|:------------------|:--------|:------|--------:|:--------------|
| regs_tl     | tlul_pkg::tl      | req_rsp | rsp   |       1 |               |


<!-- END CMDGEN -->
