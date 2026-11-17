# Hardware Interfaces

## Parameters

The following table lists the instantiation parameters of the CHERIoT memory subsystem.
The address parameters define the
[meta SRAM address map](theory_of_operation.md#meta-sram-address-map).

Parameter          | Default        | Top Earlgrey   | Description
-------------------|----------------|----------------|---------------
`addr_t`           | `logic [top_pkg::TL_AW-1:0]` | `logic [31:0]` | TL-UL address type.
`MainSramBaseAddr` | `0x1000_0000`  | `0x1000_0000`  | Base address of the main SRAM region, inclusive.
`MainSramTopAddr`  | `0x1003_0000`  | `0x1003_0000`  | Top address of the main SRAM region, exclusive.
`NvmBaseAddr`      | `0x3000_0000`  | `0x3000_0000`  | Base address of the NVM region, inclusive.
`NvmTopAddr`       | `0x3020_0000`  | `0x3020_0000`  | Top address of the NVM region, exclusive.
`MetaSramBaseAddr` | `0x1100_0000`  | `0x1100_0000`  | Base address of the unified meta SRAM.
`MemSizeRevbm`     | `3072`         | `3072`         | Size of the `revbm` window in bytes, set by topgen from the window size.
`SecLockstep`      | `1`            | `1`            | Run a second copy of the logic in [lockstep](theory_of_operation.md#lockstep) with the main copy.
`LockstepOffset`   | `1`            | `1`            | Cycles the second copy of the logic runs behind the main copy, at least 1.
`AlertAsyncOn`     | `1`            | `1`            | The alert sender is asynchronous to the alert handler.
`AlertSkewCycles`  | `1`            | `1`            | Skew cycles of the alert sender.

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
| cored_tag_h2d | prim_mubi_pkg::mubi4 | uni     | rcv   |       1 | CHERIoT capability tag carried with the A-channel of cored_tl_d.      |
| cored_tag_d2h | prim_mubi_pkg::mubi4 | uni     | req   |       1 | Capability tag returned on the D-channel of cored_tl_d.               |
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

| Alert Name   | Description                                                                                                                                                                                                                                                                                                                                                                                            |
|:-------------|:-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------|
| fatal_fault  | This fatal alert is triggered when the two copies of the lockstep disagree, when an integrity fault is detected, when a core data request carries an invalid encoding of the capability tag, when the meta SRAM path returns a device error, when the revocation engine reports a fault, when a capability store to the NVM is partial, or when a request breaks the core's capability store sequence. |

## Security Countermeasures

| Countermeasure ID                       | Description                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                        |
|:----------------------------------------|:---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------|
| CHERIOT_MEM_SYS.BUS.INTEGRITY           | End-to-end bus integrity between the Ibex lockstep and the storage cells. Relies on LOGIC.SHADOW.                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                  |
| CHERIOT_MEM_SYS.LOGIC.SHADOW            | The CHERIoT memory subsystem, including the background revocation engine, is instantiated in lockstep: with the SecLockstep parameter set (the default), a second copy of its logic runs LockstepOffset cycles behind the main copy, and a difference in their outputs other than the alert, or a fatal error of the second copy, raises the fatal_fault alert. The registers, the interrupt and the alert sender are not duplicated, so the register values are common to both copies. This also covers the pointers of the subsystem's FIFOs, which therefore are not redundantly encoded (CTR.REDUN). With SecLockstep set to 0, neither holds. |
| CHERIOT_MEM_SYS.MEM.SW_NOACCESS         | The capability tag store is not memory mapped.                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                     |
| CHERIOT_MEM_SYS.INTERSIG.MUBI           | The CHERIoT mode enable is multi-bit encoded.                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                      |
| CHERIOT_MEM_SYS.CORED_TAG.INTERSIG.MUBI | The capability tags of the core data port are multi-bit encoded between Ibex and the CHERIoT memory subsystem. Only MuBi4True reads as tagged, and a core data request with an invalid encoding raises the fatal_fault alert.                                                                                                                                                                                                                                                                                                                                                                                                                      |


<!-- END CMDGEN -->
