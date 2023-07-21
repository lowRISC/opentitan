# Interfaces

<!-- BEGIN CMDGEN util/regtool.py --interfaces ./hw/ip/flash_ctrl/data/flash_ctrl.hjson -->
Referring to the [Comportable guideline for peripheral device functionality](https://opentitan.org/book/doc/contributing/hw/comportability), the module **`flash_ctrl`** has the following hardware interfaces defined
- Primary Clock: **`clk_i`**
- Other Clocks: **`clk_otp_i`**
- Bus Device Interfaces (TL-UL): **`core_tl`**, **`prim_tl`**, **`mem_tl`**
- Bus Host Interfaces (TL-UL): *none*

## Peripheral Pins for Chip IO

| Pin name   | Direction   | Description   |
|:-----------|:------------|:--------------|
| tck        | input       | jtag clock    |
| tms        | input       | jtag tms      |
| tdi        | input       | jtag input    |
| tdo        | output      | jtag output   |

## [Inter-Module Signals](https://opentitan.org/book/doc/contributing/hw/comportability/index.html#inter-signal-handling)

| Port Name                | Package::Struct                | Type    | Act   |   Width | Description   |
|:-------------------------|:-------------------------------|:--------|:------|--------:|:--------------|
| otp                      | otp_ctrl_pkg::flash_otp_key    | req_rsp | req   |       1 |               |
| lc_nvm_debug_en          | lc_ctrl_pkg::lc_tx             | uni     | rcv   |       1 |               |
| flash_bist_enable        | prim_mubi_pkg::mubi4           | uni     | rcv   |       1 |               |
| flash_power_down_h       | logic                          | uni     | rcv   |       1 |               |
| flash_power_ready_h      | logic                          | uni     | rcv   |       1 |               |
| flash_test_mode_a        |                                | io      | none  |       2 |               |
| flash_test_voltage_h     |                                | io      | none  |       1 |               |
| lc_creator_seed_sw_rw_en | lc_ctrl_pkg::lc_tx             | uni     | rcv   |       1 |               |
| lc_owner_seed_sw_rw_en   | lc_ctrl_pkg::lc_tx             | uni     | rcv   |       1 |               |
| lc_iso_part_sw_rd_en     | lc_ctrl_pkg::lc_tx             | uni     | rcv   |       1 |               |
| lc_iso_part_sw_wr_en     | lc_ctrl_pkg::lc_tx             | uni     | rcv   |       1 |               |
| lc_seed_hw_rd_en         | lc_ctrl_pkg::lc_tx             | uni     | rcv   |       1 |               |
| lc_escalate_en           | lc_ctrl_pkg::lc_tx             | uni     | rcv   |       1 |               |
| rma_req                  | lc_ctrl_pkg::lc_tx             | uni     | rcv   |       1 |               |
| rma_ack                  | lc_ctrl_pkg::lc_tx             | uni     | req   |       1 |               |
| rma_seed                 | lc_ctrl_pkg::lc_flash_rma_seed | uni     | rcv   |       1 |               |
| pwrmgr                   | pwrmgr_pkg::pwr_flash          | uni     | req   |       1 |               |
| keymgr                   | flash_ctrl_pkg::keymgr_flash   | uni     | req   |       1 |               |
| obs_ctrl                 | ast_pkg::ast_obs_ctrl          | uni     | rcv   |       1 |               |
| fla_obs                  | logic                          | uni     | req   |       8 |               |
| core_tl                  | tlul_pkg::tl                   | req_rsp | rsp   |       1 |               |
| prim_tl                  | tlul_pkg::tl                   | req_rsp | rsp   |       1 |               |
| mem_tl                   | tlul_pkg::tl                   | req_rsp | rsp   |       1 |               |

## Interrupts

| Interrupt Name   | Type   | Description                   |
|:-----------------|:-------|:------------------------------|
| prog_empty       | Event  | Program FIFO empty            |
| prog_lvl         | Event  | Program FIFO drained to level |
| rd_full          | Event  | Read FIFO full                |
| rd_lvl           | Event  | Read FIFO filled to level     |
| op_done          | Event  | Operation complete            |
| corr_err         | Event  | Correctable error encountered |

## Security Alerts

| Alert Name             | Description                                                                                                         |
|:-----------------------|:--------------------------------------------------------------------------------------------------------------------|
| recov_err              | flash recoverable errors                                                                                            |
| fatal_std_err          | flash standard fatal errors                                                                                         |
| fatal_err              | flash fatal errors                                                                                                  |
| fatal_prim_flash_alert | Fatal alert triggered inside the flash primitive, including fatal TL-UL bus integrity faults of the test interface. |
| recov_prim_flash_alert | Recoverable alert triggered inside the flash primitive.                                                             |

## Security Countermeasures

| Countermeasure ID                          | Description                                                                                                                                                                                                                                         |
|:-------------------------------------------|:----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------|
| FLASH_CTRL.REG.BUS.INTEGRITY               | End-to-end bus integrity scheme. Since there are multiple access points for flash, please see Transmission Integrity Faults in the documentation for more details.  The bus integrity scheme for flash is different from other comportable modules. |
| FLASH_CTRL.HOST.BUS.INTEGRITY              | End-to-end bus integrity scheme. Since there are multiple access points for flash, please see Transmission Integrity Faults in the documentation for more details.  The bus integrity scheme for flash is different from other comportable modules. |
| FLASH_CTRL.MEM.BUS.INTEGRITY               | End-to-end bus integrity scheme. Since there are multiple access points for flash, please see Transmission Integrity Faults in the documentation for more details.  The bus integrity scheme for flash is different from other comportable modules. |
| FLASH_CTRL.SCRAMBLE.KEY.SIDELOAD           | The scrambling key is sideloaded from OTP and thus unreadable by SW.                                                                                                                                                                                |
| FLASH_CTRL.LC_CTRL.INTERSIG.MUBI           | Life cycle control signals are used control information partition access and flash debug access. See secret information partition, isolated information partitions and jtag connection in documentation for more details.                           |
| FLASH_CTRL.CTRL.CONFIG.REGWEN              | Configurations cannot be changed when an operation is ongoing.                                                                                                                                                                                      |
| FLASH_CTRL.DATA_REGIONS.CONFIG.REGWEN      | Each data region has a configurable regwen.                                                                                                                                                                                                         |
| FLASH_CTRL.DATA_REGIONS.CONFIG.SHADOW      | Data region configuration is shadowed.                                                                                                                                                                                                              |
| FLASH_CTRL.INFO_REGIONS.CONFIG.REGWEN      | Each info page of each type in each bank has separate regwen.                                                                                                                                                                                       |
| FLASH_CTRL.INFO_REGIONS.CONFIG.SHADOW      | Each info page is shadowed.                                                                                                                                                                                                                         |
| FLASH_CTRL.BANK.CONFIG.REGWEN              | Each bank has separate regwen for bank erase.                                                                                                                                                                                                       |
| FLASH_CTRL.BANK.CONFIG.SHADOW              | Each bank has separate regwen for bank erase.                                                                                                                                                                                                       |
| FLASH_CTRL.MEM.CTRL.GLOBAL_ESC             | Global escalation causes memory to no longer be accessible.                                                                                                                                                                                         |
| FLASH_CTRL.MEM.CTRL.LOCAL_ESC              | A subset of fatal errors cause memory to no longer be accessible. This subset is defined in [`STD_FAULT_STATUS.`](registers.md#std_fault_status)                                                                                                    |
| FLASH_CTRL.MEM_DISABLE.CONFIG.MUBI         | Software control for flash disable is multibit. The register is [`DIS.`](registers.md#dis)                                                                                                                                                          |
| FLASH_CTRL.EXEC.CONFIG.REDUN               | Software control for flash enable is 32-bit constant. The register is [`EXEC.`](registers.md#exec)                                                                                                                                                  |
| FLASH_CTRL.MEM.SCRAMBLE                    | The flash supports XEX scrambling. The cipher used is PRINCE. The scrambling scheme is enabled by software, please see flash scrambling in documentation for more details.                                                                          |
| FLASH_CTRL.MEM.INTEGRITY                   | The flash supports two layers of ECC integrity: one layer is for integrity, and the other layer is for reliability. These ECCs are enabled and disabled together by software. Please see Flash ECC in the documentation for more details.           |
| FLASH_CTRL.RMA_ENTRY.MEM.SEC_WIPE          | RMA entry entry wipes flash memory with random data.                                                                                                                                                                                                |
| FLASH_CTRL.CTRL.FSM.SPARSE                 | RMA handling FSMs in flash_ctrl_lcmgr are sparsely encoded. FSM in flash_ctrl_arb is sparsely encoded.                                                                                                                                              |
| FLASH_CTRL.PHY.FSM.SPARSE                  | PHY FSMs are sparsely encoded.                                                                                                                                                                                                                      |
| FLASH_CTRL.PHY_PROG.FSM.SPARSE             | PHY program FSMs are sparsely encoded.                                                                                                                                                                                                              |
| FLASH_CTRL.CTR.REDUN                       | flash_ctrl_lcmgr handling counters are redundantly encoded. This includes seed count and address count used during seed reading phase, as well as word count, page count and wipe index in RMA entry phase.                                         |
| FLASH_CTRL.PHY_ARBITER.CTRL.REDUN          | The phy arbiter for controller and host is redundant. The arbiter has two instance underneath that are constantly compared to each other.                                                                                                           |
| FLASH_CTRL.PHY_HOST_GRANT.CTRL.CONSISTENCY | The host grant is consistency checked. If the host is ever granted with info partition access, it is an error. If the host is ever granted at the same time as a program/erase operation, it is an error.                                           |
| FLASH_CTRL.PHY_ACK.CTRL.CONSISTENCY        | If the host or controller ever receive an unexpeced transaction acknowledge, it is an error.                                                                                                                                                        |
| FLASH_CTRL.FIFO.CTR.REDUN                  | The FIFO pointers of several FIFOs are implemented with duplicate counters.                                                                                                                                                                         |
| FLASH_CTRL.MEM_TL_LC_GATE.FSM.SPARSE       | The control FSM inside the TL-UL gating primitive is sparsely encoded.                                                                                                                                                                              |
| FLASH_CTRL.PROG_TL_LC_GATE.FSM.SPARSE      | The control FSM inside the TL-UL gating primitive is sparsely encoded.                                                                                                                                                                              |


<!-- END CMDGEN -->

## Signals

In addition to the interrupts and bus signals, the tables below lists the flash controller functional I/Os.

Signal                     | Direction      | Description
------------------------   |-----------     |---------------
`lc_creator_seed_sw_rw_en` | `input`        | Indication from `lc_ctrl` that software is allowed to read/write creator seed.
`lc_owner_seed_sw_rw_en`   | `input`        | Indication from `lc_ctrl` that software is allowed to read/write owner seed.
`lc_seed_hw_rd_en`         | `input`        | Indication from `lc_ctrl` that hardware is allowed to read creator / owner seeds.
`lc_iso_part_sw_rd_en`     | `input`        | Indication from `lc_ctrl` that software is allowed to read the isolated partition.
`lc_iso_part_sw_wr_en`     | `input`        | Indication from `lc_ctrl` that software is allowed to write the isolated partition.
`lc_escalate_en`           | `input`        | Escalation indication from `lc_ctrl`.
`lc_nvm_debug_en`          | `input`        | Indication from lc_ctrl that non-volatile memory debug is allowed.
`core_tl`                  | `input/output` | TL-UL interface used to access `flash_ctrl` registers for activating program / erase and reads to information partitions/
`prim_tl`                  | `input/output` | TL-UL interface used to access the vendor flash memory proprietary registers.
`mem_tl`                   | `input/output` | TL-UL interface used by host to access the vendor flash memory directly.
`OTP`                      | `input/output` | Interface used to request scrambling keys from `otp_ctrl`.
`rma_req`                  | `input`        | rma entry request from `lc_ctrl`.
`rma_ack`                  | `output`       | rma entry acknowlegement to `lc_ctrl`.
`rma_seed`                 | `input`        | rma entry seed.
`pwrmgr`                   | `output`       | Idle indication to `pwrmgr`.
`keymgr`                   | `output`       | Secret seed bus to `keymgr`.

In addition to the functional IOs, there are a set of signals that are directly connected to vendor flash module.

Signal                     | Direction      | Description
------------------------   |-----------     |---------------
`scan_en`                  | `input`        | scan enable
`scanmode`                 | `input`        | scan mode
`scan_rst_n`               | `input`        | scan reset
`flash_bist_enable`        | `input`        | enable flash built-in-self-test
`flash_power_down_h`       | `input`        | flash power down indication, note this is NOT a core level signal
`flash_power_ready_h`      | `input`        | flash power ready indication, note this is NOT a core level signal
`flash_test_mode_a`        | `input/output` | flash test mode io, note this is NOT a core level signal
`flash_test_voltage_h`     | `input/output` | flash test voltage, note this is NOT a core level signal
`flash_alert`              | `output`       | flash alert outputs directly to AST
