# Programmer's Guide

## Initialization

The memory inside the SRAM controller can be used right away after a system reset.
However, since the scrambling key defaults to a predefined value, it is recommended that SW performs the following initialization steps as early in the boot process as possible.

1. Request an updated ephemeral scrambling key from OTP by writing 0x1 to [`CTRL.RENEW_SCR_KEY`](registers.md#ctrl).
   SW should spin on [`STATUS.SCR_KEY_VALID`](registers.md#status) to wait until the new key has been obtained.
   While this is not strictly needed since memory accesses to the SRAM will be stalled until the updated key has been obtained, the PC value upon a watchdog crash will be more informative when using a spin wait.

2. (optional) Initialize the memory with pseudo random data by writing 0x1 to [`CTRL.INIT`](registers.md#ctrl)
   SW should spin on [`STATUS.INIT_DONE`](registers.md#status) to wait until the memory has been initialized.
   While this is not strictly needed since memory accesses to the SRAM will be stalled until the initialization is done, the PC value upon a watchdog crash will be more informative when using a spin wait.

3. (optional) Check the [`STATUS.SCR_KEY_SEED_VALID`](registers.md#status) bit:
    - In case the scrambling key seeds have been fully provisioned to OTP, this bit should be set to 0x1. A value of 0x0 indicates that the OTP could be malfunctioning or has been tampered with.
    - If the scrambling seeds have not yet been provisioned to OTP, this bit is set to 0x0. The scrambling key will in that case still be ephemeral, but the key seed mixed in as part of the key derivation process will be set to a predefined netlist constant.

4. (optional) Enable the read-modify-write integrity check by writing kMultiBitBool4True to [`RMW_INTG_CHECK.EN`](registers.md#rmw_intg_check) and lock it by writing to [`RMW_INTG_CHECK_REGWEN`](registers.md#rmw_intg_check_regwen).
   This must only be done once every word of the memory holds valid integrity bits, e.g., after the initialization in step 2 has completed.
   Otherwise, a sub-word write to a location that has not been initialized triggers a fatal error.
   Note that requesting a new scrambling key without re-initializing the memory afterwards leaves the memory without valid integrity bits.
   Hence, SW should either lock [`CTRL`](registers.md#ctrl) as described in step 5, or always re-initialize the memory after a key renewal.
   For memories whose contents are retained across resets, the check must only be re-enabled if the memory has been initialized since the last key renewal.

5. (optional) Lock down write access to [`CTRL`](registers.md#ctrl) by writing to [`CTRL_REGWEN`](registers.md#ctrl_regwen) if future key renewals and initializations should be disallowed until the next system reset.

Note that before (re-)requesting an updated SRAM key it is imperative to make sure that:
- The memory contents are not needed anymore. Requesting a key implicitly wipes all data in the SRAM.
- The CSRNG and the entropy distribution network have been initialized. The key derivation mechanism in OTP needs to request a chunk of fresh entropy, and that request will block until the entropy distribution network responds.

It should also be noted that data and address scrambling is never entirely disabled - even when the default scrambling key is used.

## Accesses Outside of the Implemented Memory Range

Depending on the configured memory size, the address range decoded by the memory can be larger than the implemented memory, e.g., if `MemSizeRam` is not a power of 2.
Accesses to an address inside that range but beyond `MemSizeRam` are answered with a TL-UL error response, and the memory is not accessed.

## Device Interface Functions (DIFs)

- [Device Interface Functions](../../../../sw/device/lib/dif/dif_sram_ctrl.h)
