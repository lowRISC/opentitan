# Hardware Interfaces

## Parameters

The following table lists the instantiation parameters of the backdoor loader.

Parameter                   | Default               | Top Earlgrey      | Description
----------------------------|-----------------------|-------------------|---------------
`NumBkdrTgts`               | 8                     | 8                 | Number of RAM targets supported.
`MaxWordWidthDiv32`         | 4                     | 4                 | Supports up to 128-bit words.

## Signals

Referring to the [Comportable guideline for peripheral device functionality](https://opentitan.org/book/doc/contributing/hw/comportability), the module **`bkdr_loader`** has the following hardware interfaces defined
- Primary Clock: **`clk_i`**
- Other Clocks: *none*
- Bus Device Interfaces (TL-UL): *none*
- Bus Host Interfaces (TL-UL): *none*
- Peripheral Pins for Chip IO: *none*
- Interrupts: *none*
- Security Alerts: *none*
- Security Countermeasures: *none*
