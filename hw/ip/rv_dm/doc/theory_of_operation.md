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


## Late Debug Enable Mechanism

The RV_DM is gated by life cycle so that it is only usable during TEST_UNLOCKED*, DEV and RMA life cycle states where the LC_HW_DEBUG_EN signal is asserted.
In the DEV life cycle state, this gating mechanism supports "late enablement" via firmware in order to implement a debug policy where ROM or ROM_EXT first secures and locks critical regions, assets and mechanisms in the device before ungating the RV_DM completely.

The following truth table summarizes the behavior of this mechanism

LC State                     | DIS_RV_DM_LATE_DEBUG (OTP Fuse) | LATE_DEBUG_ENABLE (CSR) | RV_DM reachable via TAP | RV_DM fully ungated
-----------------------------|---------------------------------|-------------------------|-------------------------|--------------------
TEST_UNLOCKED* or RMA        | x                               | x                       | yes                     | yes
PROD*, RAW or invalid states | x                               | x                       | no                      | no
DEV                          | kMuBi8True                      | x                       | yes                     | yes
DEV                          | not kMuBi8True                  | not kMuBi32True         | yes                     | no
DEV                          | not kMuBi8True                  | kMuBi32True             | yes                     | yes

### Non-debug Module Reset Support

The life cycle gating mechanism explained in the previous section cuts the connection between the RV_DM and a JTAG attached debugger whenever the device is reset.
In order to prevent this from happening during a non-debug-module (NDM) reset request, the TAP/JTAG-side gating logic is modulated using a latched version of the debug enable signal.
When using a dedicated JTAG TAP in the debug module, e.g., in Earlgrey, the debug enable signal that comes from the strap sampling module inside the pinmux.
The pinmux basically ensures that that signal is latched and kept stable while an NDM reset is taking place.
See also [pinmux documentation](../../../top_earlgrey/ip_autogen/pinmux/doc/theory_of_operation.md#strap-sampling-and-tap-isolation).
When using the debug module with the DMI interface, e.g., in Darjeeling, the debug module itself latches the debug enable signal while the NDM reset is taking place.
