# Hardware Interfaces

## Parameters

The following table lists the instantiation parameters of the CHERIoT memory subsystem.
[Theory of Operation](theory_of_operation.md#meta-sram-address-map).

Parameter          | Default        | Top Earlgrey   | Description
-------------------|----------------|----------------|---------------
`addr_t`           | `logic [top_pkg::TL_AW-1:0]` | `logic [31:0]` | TL-UL address type.
`MainSramBaseAddr` | `0x1000_0000`  | `0x1000_0000`  | Base address of the main SRAM region, inclusive.
`MainSramTopAddr`  | `0x1002_0000`  | `0x1002_0000`  | Top address of the main SRAM region, exclusive.
`NvmBaseAddr`      | `0x2000_0000`  | `0x2000_0000`  | Base address of the NVM region, inclusive.
`NvmTopAddr`       | `0x2020_0000`  | `0x2020_0000`  | Top address of the NVM region, exclusive.
`MetaSramBaseAddr` | `0x0000_0000`  | `0x1100_0000`  | Base address of the unified meta SRAM.

## Signals

<!-- BEGIN CMDGEN util/regtool.py --interfaces ./hw/ip/cheriot/data/cheriot.hjson -->
Referring to the [Comportable guideline for peripheral device functionality](https://opentitan.org/book/doc/contributing/hw/comportability), the module **`cheriot`** has the following hardware interfaces defined
- Primary Clock: **`clk_i`**
- Other Clocks: *none*
- Bus Device Interfaces (TL-UL): **`regs_tl_d`**, **`revbm_tl_d`**
- Bus Host Interfaces (TL-UL): **`cored_tl_h`**
- Peripheral Pins for Chip IO: *none*
- Interrupts: *none*

## [Inter-Module Signals](https://opentitan.org/book/doc/contributing/hw/comportability/index.html#inter-signal-handling)

| Port Name     | Package::Struct      | Type    | Act   |   Width | Description                                                           |
|:--------------|:---------------------|:--------|:------|--------:|:----------------------------------------------------------------------|
| cheriot_ena   | prim_mubi_pkg::mubi4 | uni     | rcv   |       1 | CHERIoT mode enable.                                                  |
| cored_tl_d    | tlul_pkg::tl         | req_rsp | rsp   |       1 | Data port from the core.                                              |
| cored_tag_h2d | logic                | uni     | rcv   |       1 | CHERIoT capability tag carried with the A-channel of cored_h.         |
| cored_tag_d2h | logic                | uni     | req   |       1 | Capability tag returned on the D-channel of cored_h.                  |
| corerevbm_tl  | tlul_pkg::tl         | req_rsp | rsp   |       1 | TRVK (tag revocation) revocation bitmap port from the core.           |
| meta_sram_tl  | tlul_pkg::tl         | req_rsp | req   |       1 | Host TL-UL port to the external meta SRAM controller's RAM interface. |
| cored_tl_h    | tlul_pkg::tl         | req_rsp | req   |       1 |                                                                       |
| regs_tl_d     | tlul_pkg::tl         | req_rsp | rsp   |       1 |                                                                       |
| revbm_tl_d    | tlul_pkg::tl         | req_rsp | rsp   |       1 |                                                                       |

## Security Alerts

| Alert Name   | Description                                                                                                                           |
|:-------------|:--------------------------------------------------------------------------------------------------------------------------------------|
| fatal_fault  | This fatal alert is triggered when an integrity fault is detected or when the tag  filter's transaction FIFO reports a pointer error. |

## Security Countermeasures

| Countermeasure ID       | Description                                                                                     |
|:------------------------|:------------------------------------------------------------------------------------------------|
| CHERIOT.BUS.INTEGRITY   | End-to-end bus integrity between the Ibex lockstep  and the storage cells.                      |
| CHERIOT.LOGIC.SHADOW    | The CHERIoT subsystem is instantiated in lockstep.                                              |
| CHERIOT.MEM.SW_NOACCESS | The capability tag store is not memory mapped.                                                  |
| CHERIOT.INTERSIG.MUBI   | The CHERIoT mode enable is multi-bit encoded.                                                   |
| CHERIOT.CTR.REDUN       | The tag filter's outstanding-transaction FIFO uses redundantly encoded read and write pointers. |


<!-- END CMDGEN -->
