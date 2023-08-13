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
