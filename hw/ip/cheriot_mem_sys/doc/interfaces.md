# Hardware Interfaces

## Parameters

The following table lists the instantiation parameters of the CHERIoT memory subsystem.
The [meta SRAM address map](theory_of_operation.md#meta-sram-address-map) follows from the address parameters.

Parameter          | Default        | Top Earlgrey   | Description
-------------------|----------------|----------------|---------------
`addr_t`           | `logic [top_pkg::TL_AW-1:0]` | `logic [31:0]` | TL-UL address type.
`MainSramBaseAddr` | `0x1000_0000`  | `0x1000_0000`  | Base address of the main SRAM region, inclusive.
`MainSramTopAddr`  | `0x1003_0000`  | `0x1003_0000`  | Top address of the main SRAM region, exclusive.
`NvmBaseAddr`      | `0x3000_0000`  | `0x3000_0000`  | Base address of the NVM region, inclusive.
`NvmTopAddr`       | `0x3020_0000`  | `0x3020_0000`  | Top address of the NVM region, exclusive.
`MetaSramBaseAddr` | `0x1100_0000`  | `0x1100_0000`  | Base address of the unified meta SRAM.
`MemSizeRevbm`     | `3072`         | `3072`         | Size of the `revbm` window in bytes, set by topgen. Must equal the size of the main SRAM revocation bitmap.
`AlertAsyncOn`     | `1'b1`         | `1'b1`         | Adds synchronizers to the alert sender for an alert handler on another clock, set by topgen.
`AlertSkewCycles`  | `1`            | `1`            | Cycles of skew tolerated on the differential alert signals, set by topgen.

## Supported Parameter Sets

The design is signed off with the parameters Earl Grey instantiates, listed in the Top Earlgrey column above.
The address parameters follow the Earl Grey memory map and can change with it.

## Signals

<!-- BEGIN CMDGEN util/regtool.py --interfaces ./hw/ip/cheriot_mem_sys/data/cheriot_mem_sys.hjson -->
Referring to the [Comportable guideline for peripheral device functionality](https://opentitan.org/book/doc/contributing/hw/comportability), the module **`cheriot_mem_sys`** has the following hardware interfaces defined
- Primary Clock: **`clk_i`**
- Other Clocks: *none*
- Bus Device Interfaces (TL-UL): **`regs_tl_d`**, **`revbm_tl_d`**
- Bus Host Interfaces (TL-UL): **`cored_tl_h`**, **`tbre_tl_h`**
- Peripheral Pins for Chip IO: *none*

## [Inter-Module Signals](https://opentitan.org/book/doc/contributing/hw/comportability/index.html#inter-signal-handling)

| Port Name     | Package::Struct      | Type    | Act   |   Width | Description                                                           |
|:--------------|:---------------------|:--------|:------|--------:|:----------------------------------------------------------------------|
| cheriot_ena   | prim_mubi_pkg::mubi4 | uni     | rcv   |       1 | CHERIoT mode enable.                                                  |
| cored_tl_d    | tlul_pkg::tl         | req_rsp | rsp   |       1 | Data port from the core.                                              |
| cored_tag_h2d | logic                | uni     | rcv   |       1 | CHERIoT capability tag carried with the A-channel of cored_tl_h.      |
| cored_tag_d2h | logic                | uni     | req   |       1 | Capability tag returned on the D-channel of cored_tl_h.               |
| corerevbm_tl  | tlul_pkg::tl         | req_rsp | rsp   |       1 | TRVK (tag revocation) revocation bitmap port from the core.           |
| meta_sram_tl  | tlul_pkg::tl         | req_rsp | req   |       1 | Host TL-UL port to the external meta SRAM controller's RAM interface. |
| cored_tl_h    | tlul_pkg::tl         | req_rsp | req   |       1 |                                                                       |
| tbre_tl_h     | tlul_pkg::tl         | req_rsp | req   |       1 |                                                                       |
| regs_tl_d     | tlul_pkg::tl         | req_rsp | rsp   |       1 |                                                                       |
| revbm_tl_d    | tlul_pkg::tl         | req_rsp | rsp   |       1 |                                                                       |

## Interrupts

| Interrupt Name   | Type   | Description                                                                 |
|:-----------------|:-------|:----------------------------------------------------------------------------|
| tbre_done        | Event  | Raised when the revocation engine has resolved every capability of a sweep. |

## Security Alerts

| Alert Name   | Description                                                                                                                                                                                                                                                                  |
|:-------------|:-----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------|
| fatal_fault  | This fatal alert is triggered when an integrity fault is detected, when the meta SRAM path returns a device error, when the revocation engine reports a fault, when a capability store to the NVM is partial, or when a request breaks the core's capability store sequence. |

## Security Countermeasures

| Countermeasure ID                       | Description                                                                                                                                                                                                                                  |
|:----------------------------------------|:---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------|
| CHERIOT_MEM_SYS.BUS.INTEGRITY           | End-to-end bus integrity between the Ibex lockstep and the storage cells. Relies on LOGIC.SHADOW, which is not implemented yet.                                                                                                              |
| CHERIOT_MEM_SYS.LOGIC.SHADOW            | The CHERIoT memory subsystem, including the background revocation engine, is instantiated in lockstep. Not implemented yet. This also covers the pointers of the subsystem's FIFOs, which therefore are not redundantly encoded (CTR.REDUN). |
| CHERIOT_MEM_SYS.MEM.SW_NOACCESS         | The capability tag store is not memory mapped.                                                                                                                                                                                               |
| CHERIOT_MEM_SYS.INTERSIG.MUBI           | The CHERIoT mode enable is multi-bit encoded.                                                                                                                                                                                                |
| CHERIOT_MEM_SYS.CORED_TAG.INTERSIG.MUBI | The capability tag is multi-bit encoded between the Ibex lockstep domain and the lockstep domain of the CHERIoT memory subsystem. Not implemented yet.                                                                                       |


<!-- END CMDGEN -->
