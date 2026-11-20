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


## CHERIoT Mode

The debug module supports RV32I and CHERIoT harts if the `CheriotSupport` parameter is set.
In that case, `cheriot_ena_i` selects the mode at runtime and only selects CHERIoT with `MuBi4True`.
The mode must not change while a hart is halted.
In Earl Grey, `rv_core_ibex` drives `cheriot_ena_i` and switches from RV32I to CHERIoT once.
In CHERIoT mode:

- A separate CHERIoT debug ROM is used.
- Abstract commands save and restore their scratch registers with `CSpecialRW`, so borrowed capabilities keep their tags.
- `aarsize == 3` is supported and transfers a capability without its tag: address in `data0`, metadata in `data1`.

Register mapping for `aarsize == 3` in CHERIoT mode:

- A GPR (`regno` 0x1000 to 0x101f) transfers the address and metadata of the capability held in that register.
- `regno` 0x0 to 0x1f accesses the Special Capability Register (SCR). Higher `regno` values in the CSR range are rejected as unsupported.

Limitations of CHERIoT mode:

- Tags are not transported through `data0`/`data1` in either direction.
  A read does not return the tag and a capability written by the debugger is untagged.
  This includes GPRs written from GDB.
  To check a tag, the debugger can run `cgettag` in the program buffer and read the result back.
  This needs a scratch GPR for the result.
  Unlike the scratch registers of abstract commands, the debugger saves this one through `data0`/`data1` (as current OpenOCD does), not in an SCR, so it loses its own tag.
- SBA bypasses the CHERIoT tag filter and does not clear tags on writes.
- In debug mode, Ibex disables its CHERIoT bounds and permission checks, so it can access any memory.
- The debug module is currently not designed to protect capabilities and must never be used in a system that relies on capabilities to protect production assets.

This follows the abstract command interface of the CHERIoT-Platform `cheriot-dbg-module`, so the debugger must be CHERIoT-aware.
OpenTitan's host tooling (`util/openocd/`, `opentitanlib`) does not support CHERIoT mode yet.
Stock OpenOCD is not CHERIoT-aware: if it connects after the mode switch, its 64-bit probe read of `s0` succeeds, so it treats the hart as RV64.
Connecting it before the mode switch allows basic debugging with 32-bit register accesses, but only with `riscv set_mem_access sysbus`, as in `util/openocd/target/lowrisc-earlgrey.cfg`.
Otherwise, OpenOCD accesses memory through the program buffer and saves and restores `s0`, `s1` and `s2` with 32-bit accesses, which clears their tags.

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
In that case, the debug module clears the latched value whenever any of `lc_hw_debug_clr`, `lc_check_byp_en` or `lc_escalate_en` is not Off.
See also [HW_DEBUG_CLR](../../lc_ctrl/doc/theory_of_operation.md#hw_debug_clr) in the life cycle controller documentation.
