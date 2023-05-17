# Theory of Operation

## Memory Maps

### TL-UL device
The memory map accessible over the TL-UL device interface is documented in the [Debug Memory](https://github.com/lowRISC/opentitan/blob/master/hw/vendor/pulp_riscv_dbg/doc/debug-system.md#debug-memory) section of the [PULP RISC-V Debug System Documentation](https://github.com/lowRISC/opentitan/blob/master/hw/vendor/pulp_riscv_dbg/doc/debug-system.md).
Note this contains a mixture of read only and read-write regions and which is which isn't documented.
The read-write regions are:

 - ``0x100`` - ``0x10c``: Halted, Going, Resuming, Exception
 - ``0x380`` - ``0x382``: DataAddr (``0x383 - 0x338`` are not implemented and will read undefined data)

All other regions are read only.

### Debug Module Registers

The [Debug Module Registers](https://github.com/lowRISC/opentitan/blob/master/hw/vendor/pulp_riscv_dbg/doc/debug-system.md#debug-module-registers) are only accessible via the Debug Module Interface (DMI) accessed via JTAG.
There is no access to these via the TL-UL device interface.

## Hardware Interfaces

All hardware interfaces of the debug system are documented in the [PULP RISC-V Debug System Documentation](https://github.com/lowRISC/opentitan/blob/master/hw/vendor/pulp_riscv_dbg/doc/debug-system.md), with the exception of the bus interfaces, which are converted to TL-UL by this wrapper.

### Signals

* [Interface Tables](../data/rv_dm.hjson#interfaces)

### Life Cycle Control

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

### JTAG

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

### System interface

The debug system is able to reset the system through its JTAG connection; the non-debug module reset (`ndmreset_req_o`) signals this intent.
It is up to the larger system design to specify which parts of the system are actually reset by this signal.

The `dmactive_o` signals that some kind of debugging is ongoing.
Use this signal to prevent the power down of the core and bus-attached peripherals, which might be accessed by the debug system.

```verilog
output logic                  ndmreset_o,  // non-debug module reset
output logic                  dmactive_o,  // debug module is active
```

### Core interface

Most communication between the core and the debug system is performed through the debug memory.
To enter debug mode due to an external debug request, the debug system provides a `debug_req_o` interrupt.
If the core is unavailable to the debug system, e.g. because it is powered down or in a locked-down state, the `unavailable_i` signal can signal this condition to the debug system.

```verilog
output logic [NrHarts-1:0]    debug_req_o, // async debug request
input  logic [NrHarts-1:0]    unavailable_i, // communicate whether the hart is unavailable
                                             // (e.g.: power down)
```

### TL-UL device for debug memory

The debug system implements execution-based debug according to the RISC-V Debug Specification.
Most interactions between the core and the debug system are performed through the debug memory, a bus-exposed memory.
The memory needs to be accessible from the core instruction *and* data interfaces.
A full memory map is part of the [PULP RISC-V Debug System Documentation](https://github.com/lowRISC/opentitan/blob/master/hw/vendor/pulp_riscv_dbg/doc/debug-system.md).

```verilog
input  tlul_pkg::tl_h2d_t tl_d_i,
output tlul_pkg::tl_d2h_t tl_d_o,
```

### TL-UL host for System Bus Access (SBA)

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
