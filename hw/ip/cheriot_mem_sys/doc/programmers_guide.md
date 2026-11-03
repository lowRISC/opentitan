# Programmer's Guide

This section details how software drives the background revocation engine (TBRE) of the CHERIoT memory subsystem, and how capabilities are stored in the NVM.
The tag store and the rest of the meta SRAM are not software-visible; software only writes the revocation bitmap through the `revbm` window and controls the engine through its [registers](registers.md).

## Revoking Capabilities

1.  **Mark the freed memory as revoked:** Set the revocation bit of every 8-byte granule of the freed allocation in the `revbm` window, as described in the [Theory of Operation](theory_of_operation.md#meta-sram-address-map).
2.  **Check the engine is idle:** `TBRE_STATUS.busy` in [`TBRE_STATUS`](registers.md#tbre_status) must read zero; while it is set, [`TBRE_REGWEN`](registers.md#tbre_regwen) is low and writes to the sweep registers are ignored.
3.  **Describe the sweep:** Write the address of the first capability to [`TBRE_BASE_ADDR`](registers.md#tbre_base_addr) and the number of capabilities to [`TBRE_NUM_CAPS`](registers.md#tbre_num_caps).
    The address is 8-byte aligned by construction and must lie in a tagged region, the main SRAM or the NVM; a sweep reaching past the top of its region ends there.
    A capability to the freed memory can be stored in either region.
    The topmost NVM pages (the emulated OTP, from `0x301F_F600` in Earl Grey) are not accessible to software and cannot be read, so sweeping them results in an error; end NVM sweeps below them.
4.  **Start the sweep:** Write 1 to [`TBRE_START`](registers.md#tbre_start).
    The start is ignored outside CHERIoT mode, with `TBRE_NUM_CAPS` zero, or with `TBRE_BASE_ADDR` outside the tagged regions.
    An ignored start sets `TBRE_STATUS.start_err`, which software clears by writing 1 to it; check it after a start to tell an ignored start from a completed sweep.
5.  **Wait for completion:** Enable the `tbre_done` interrupt in [`INTR_ENABLE`](registers.md#intr_enable) and wait for it, or poll `TBRE_STATUS.busy` until it reads zero.
    Both happen once every capability of the sweep has been resolved.
    Acknowledge the interrupt by writing 1 to [`INTR_STATE`](registers.md#intr_state).
6.  **Sweep the other region:** Repeat steps 2 to 5 for the other tagged region.
7.  **Release the memory:** Clear the revocation bits set in step 1 before the memory is handed out again.

The engine reads both words of every capability and clears the tag of each tagged, non-sealing capability whose base has its revocation bit set.
It never modifies memory data, and capabilities whose base lies outside the main SRAM region are never revoked.
A capability the core writes while the engine resolves it keeps the tag the core wrote; writes by other crossbar hosts, such as the debug module's system bus access, are not watched.

## Tracking Completed Sweeps

[`TBRE_EPOCH`](registers.md#tbre_epoch): odd while a sweep runs, and advanced by two for every sweep that ended without an error.
An allocator records the epoch when it frees memory and reuses the memory once a sweep of each tagged region that started later has ended without an error.
If software sweeps the main SRAM and the NVM in turn and repeats a sweep that ended with an error for the same region, any two consecutive sweeps that ended without an error cover both regions: with `distance` the signed difference between the current and the recorded epoch, the memory may be reused once `distance > 3 + (recorded & 1)`.
To start a sweep, write 1 to `TBRE_START` only if the epoch is even; a start written while a sweep runs, or ignored, leaves the epoch unchanged, so starts from several threads need no lock.
A sweep that ends with an error does not advance the epoch, so the waiting allocator starts another one instead of reusing the memory.
`TBRE_EPOCH`, `TBRE_REGWEN` and `TBRE_STATUS.busy` are all safe to read right after the start, as the first read the register interface accepts already shows the sweep; `TBRE_STATUS.busy` follows the other two one cycle later.

The `tbre_done` interrupt is a level interrupt: `INTR_STATE` stays set until software writes 1 to it.
Clear it on every wake before completing the interrupt, and re-check completion after enabling the interrupt, since a sweep ending in the cycle `INTR_STATE` is cleared does not set it again.

## Storing Capabilities in the NVM

The NVM is not written through the interconnect, so a capability store (`csc`) to it cannot write data.
It sets the capability's tag if the NVM already holds exactly the 64 bits being stored, so software first programs the capability's two words through the NVM controller and then stores the same capability with `csc` to give it its tag.
A `csc` of a tagged capability holding other data to the NVM is answered with a bus error, a store access fault in the core, and leaves the tag as it was.
A plain store to the NVM, or a `csc` of an untagged capability, is refused by the NVM and clears the tag of the capability it targets.

Reprogramming NVM content through the NVM controller does not pass the tag filter, so a tag stays valid on the new contents.
The compartment that reprograms NVM content through the NVM controller (i.e., with data not flowing through the CHERIoT memory subsystem) **must** ensure that invalid tags are cleared, by a plain store (e.g. `sw`) through the core to each affected capability.
The NVM refuses the store, but the tag filter clears the tag.

## Errors

A read of the swept memory answered with an error, e.g. of a read-protected NVM page, leaves that word's tag alone.
An error or integrity fault on any other response to the engine, or a fault of the RMW filter during a sweep, raises the `fatal_fault` alert; a failed bitmap lookup counts as revoked.
All of them set `TBRE_STATUS.sweep_err`, which software clears by writing 1 to it; check it once a sweep completes, since a sweep with an error may have left revoked capabilities tagged.
`TBRE_STATUS.start_err` only reports ignored starts.
