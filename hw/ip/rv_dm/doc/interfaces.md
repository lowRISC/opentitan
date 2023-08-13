# Hardware Interfaces

All hardware interfaces of the debug system are documented in the [PULP RISC-V Debug System Documentation](https://github.com/lowRISC/opentitan/blob/master/hw/vendor/pulp_riscv_dbg/doc/debug-system.md), with the exception of the bus interfaces, which are converted to TL-UL by this wrapper.

## Signals

<!-- BEGIN CMDGEN util/regtool.py --interfaces ./hw/ip/rv_dm/data/rv_dm.hjson -->
Referring to the [Comportable guideline for peripheral device functionality](https://opentitan.org/book/doc/contributing/hw/comportability), the module **`rv_dm`** has the following hardware interfaces defined
- Primary Clock: **`clk_i`**
- Other Clocks: *none*
- Bus Device Interfaces (TL-UL): **`regs_tl_d`**, **`mem_tl_d`**
- Bus Host Interfaces (TL-UL): **`sba_tl_h`**
- Peripheral Pins for Chip IO: *none*
- Interrupts: *none*

## [Inter-Module Signals](https://opentitan.org/book/doc/contributing/hw/comportability/index.html#inter-signal-handling)

| Port Name          | Package::Struct                    | Type    | Act   |   Width | Description                                                                                                                                                                                                                                                                         |
|:-------------------|:-----------------------------------|:--------|:------|--------:|:------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------|
| jtag               | jtag_pkg::jtag                     | req_rsp | rsp   |       1 | JTAG signals for the RISC-V TAP.                                                                                                                                                                                                                                                    |
| lc_hw_debug_en     | lc_ctrl_pkg::lc_tx                 | uni     | rcv   |       1 | Multibit life cycle hardware debug enable signal coming from life cycle controller, asserted when the hardware debug mechanisms are enabled in the system.                                                                                                                          |
| pinmux_hw_debug_en | lc_ctrl_pkg::lc_tx                 | uni     | rcv   |       1 | Multibit life cycle hardware debug enable signal coming from pinmux. This is a latched version of the lc_hw_debug_en signal and is only used to gate the JTAG / TAP side of the RV_DM. It is used to keep a debug session live while the rest of the system undergoes an NDM reset. |
| unavailable        | logic                              | uni     | rcv   |       1 | This signal indicates to the debug module that the main processor is not available for debug (e.g. due to a low-power state).                                                                                                                                                       |
| ndmreset_req       | logic                              | uni     | req   |       1 | Non-debug module reset request going to the system reset infrastructure.                                                                                                                                                                                                            |
| dmactive           | logic                              | uni     | req   |       1 | This signal indicates whether the debug module is active and can be used to prevent power down of the core and bus-attached peripherals.                                                                                                                                            |
| debug_req          | logic [rv_dm_reg_pkg::NrHarts-1:0] | uni     | req   |       1 | This is the debug request interrupt going to the main processor.                                                                                                                                                                                                                    |
| sba_tl_h           | tlul_pkg::tl                       | req_rsp | req   |       1 |                                                                                                                                                                                                                                                                                     |
| regs_tl_d          | tlul_pkg::tl                       | req_rsp | rsp   |       1 |                                                                                                                                                                                                                                                                                     |
| mem_tl_d           | tlul_pkg::tl                       | req_rsp | rsp   |       1 |                                                                                                                                                                                                                                                                                     |

## Security Alerts

| Alert Name   | Description                                                                       |
|:-------------|:----------------------------------------------------------------------------------|
| fatal_fault  | This fatal alert is triggered when a fatal TL-UL bus integrity fault is detected. |

## Security Countermeasures

| Countermeasure ID                  | Description                                                                                                                                                                                                                                                                                                                                                                                                                                                            |
|:-----------------------------------|:-----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------|
| RV_DM.BUS.INTEGRITY                | End-to-end bus integrity scheme.                                                                                                                                                                                                                                                                                                                                                                                                                                       |
| RV_DM.LC_HW_DEBUG_EN.INTERSIG.MUBI | The life cycle hardware debug enable signal is multibit encoded.                                                                                                                                                                                                                                                                                                                                                                                                       |
| RV_DM.DM_EN.CTRL.LC_GATED          | The debug module is enabled with the LC_HW_DEBUG_EN signal. This enablement is implemented by gating / enabling critical blocks with separately buffered copies of the life cycle signal. This comprises the debug module interface (DMI) attached to the TAP, the reset request line, the system bus access module (SBA), the debug request output, the TL-UL adapter for the debug ROM, and the ifetch indicator being fed into the TL-UL adapter for the debug ROM. |
| RV_DM.SBA_TL_LC_GATE.FSM.SPARSE    | The control FSM inside the TL-UL gating primitive is sparsely encoded.                                                                                                                                                                                                                                                                                                                                                                                                 |
| RV_DM.MEM_TL_LC_GATE.FSM.SPARSE    | The control FSM inside the TL-UL gating primitive is sparsely encoded.                                                                                                                                                                                                                                                                                                                                                                                                 |
| RV_DM.EXEC.CTRL.MUBI               | The instruction fetch enable signal that is modulated with LC_HW_DEBUG_EN and that feeds into the TL-UL adapter is multibit encoded.                                                                                                                                                                                                                                                                                                                                   |


<!-- END CMDGEN -->

## Life Cycle Control

Debug system functionality is controlled by the [HW_DEBUG_EN](../../lc_ctrl/README.md#hw_debug_en) function of the life cycle controller.
Note that in order to support the non-debug module (NDM) reset functionality, there are two HW_DEBUG_EN signal inputs in the `rv_dm` module:

```verilog
  input  lc_ctrl_pkg::lc_tx_t lc_hw_debug_en_i,
  input  lc_ctrl_pkg::lc_tx_t pinmux_hw_debug_en_i,
```

The first one comes directly from the life cycle controller and is a "live" value, decoded from the current life cycle state.
The second one is a latched version coming from the [strap sampling and TAP selection logic inside the pinmux](../../pinmux/doc/theory_of_operation.md#strap-sampling-and-tap-isolation).
In addition to the power, reset and clock managers, the `rv_dm` and the TAP selection logic in the pinmux are the only parts of the system that do not get reset when an NDM reset is triggered (see also [reset manager documentation](../../rstmgr/doc/theory_of_operation.md#system-reset-tree)).
The latched variant of the signal allows to keep the JTAG side of the debug module operational while the rest of the system (including the life cycle controller) undergoes a reset cycle.

## JTAG

The debug system provides a standard JTAG (IEEE Std 1149.1-2013) port for external debug access.
All JTAG logic is clocked with an externally supplied test clock (`tck`).
The protocol used for this JTAG port is specified in the RISC-V Debug Specification as JTAG Debug Transport Module (DTM).

```verilog
input  logic               tck_i,           // JTAG test clock pad
input  logic               tms_i,           // JTAG test mode select pad
input  logic               trst_ni,         // JTAG test reset pad
input  logic               td_i,            // JTAG test data input pad
output logic               td_o,            // JTAG test data output pad
output logic               tdo_oe_o         // Data out output enable
```

## System interface

The debug system is able to reset the system through its JTAG connection; the non-debug module reset (`ndmreset_req_o`) signals this intent.
It is up to the larger system design to specify which parts of the system are actually reset by this signal.

The `dmactive_o` signals that some kind of debugging is ongoing.
Use this signal to prevent the power down of the core and bus-attached peripherals, which might be accessed by the debug system.

```verilog
output logic                  ndmreset_o,  // non-debug module reset
output logic                  dmactive_o,  // debug module is active
```

## Core interface

Most communication between the core and the debug system is performed through the debug memory.
To enter debug mode due to an external debug request, the debug system provides a `debug_req_o` interrupt.
If the core is unavailable to the debug system, e.g. because it is powered down or in a locked-down state, the `unavailable_i` signal can signal this condition to the debug system.

```verilog
output logic [NrHarts-1:0]    debug_req_o, // async debug request
input  logic [NrHarts-1:0]    unavailable_i, // communicate whether the hart is unavailable
                                             // (e.g.: power down)
```

## TL-UL device for debug memory

The debug system implements execution-based debug according to the RISC-V Debug Specification.
Most interactions between the core and the debug system are performed through the debug memory, a bus-exposed memory.
The memory needs to be accessible from the core instruction *and* data interfaces.
A full memory map is part of the [PULP RISC-V Debug System Documentation](https://github.com/lowRISC/opentitan/blob/master/hw/vendor/pulp_riscv_dbg/doc/debug-system.md).

```verilog
input  tlul_pkg::tl_h2d_t tl_d_i,
output tlul_pkg::tl_d2h_t tl_d_o,
```

## TL-UL host for System Bus Access (SBA)

Bus-attached peripherals can be accessed through the debug system, a functionality called System Bus Access (SBA) in the RISC-V Debug Specification.
It is up to the interconnect fabric to decide which peripherals are actually accessible.
The debug system wrapper provides a TL-UL host bus interface for SBA.

Note, when bus errors (either address errors or integrity errors) occur on the SBA TL-UL path, alerts are not triggered.
Instead the error status is fed into the PULP RISC-V Debug System for status indication.


```verilog
// bus host, for system bus accesses
output tlul_pkg::tl_h2d_t  tl_h_o,
input  tlul_pkg::tl_d2h_t  tl_h_i,
```
