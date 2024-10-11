# Programmer's Guide

Before initiating any of the following key generation operations, it is recommended (but not mandatory) to check that keymgr_dpe is ready to handle them.
Except for the first advance call that initializes keymgr_dpe, this means keymgr_dpe is idle (as reported in `OP_STATUS`) and FSM is in `Available` state (reported in `WORKING_STATE`).

Similarly, at the end of the operation (when `OP_STATUS` is not `WIP` anymore), it is recommended to check that the operation was successful by reading `ERR_CODE`.
SW can also read the reported FSM state through `WORKING_STATE` to confirm that keymgr_dpe reaches the expected state.

## Initialize (first advance call)

From a SW perspective, there is not an explicit initialize command.
Initialization is simply the first advance call.
The first advance call only latches the OTP creator root key, therefore most registers used in the regular advance call are ignored during initialization.

Keymgr_DPE is initialized by configuring the following CSR:
*  Set `CONTROL_SHADOWED.OPERATION` to `Advance`.
*  Set `CONTROL_SHADOWED.SLOT_DST_SEL` to the destination slot to which UDS should be latched.
*  Set `START` to initiate the operation.

At the end of the successful first advance call, the UDS is latched into the specified destination slot.

## Advance

This section specifically addresses the advance calls after initialization (i.e. when `WORKING_STATE` is reported as `Available`).
The advance operation is executed by configuring the following CSR:

*  Set `SW_BINDING`.
*  Set `SW_BINDING_REGWEN` to zero, if modifications on `SW_BINDING` needs to be prevented until the next advance call.
*  Set `MAX_KEY_VER_SHADOWED`.
*  Set `MAX_KEY_VER_REGWEN` to zero, if modifications on `MAX_KEY_VER_SHADOWED` needs to be prevented until the next advance call.
*  Set `SLOT_POLICY` to control policy fields of the generated child slot.
*  Set `SLOT_POLICY_REGWEN` to zero, if modifications on `SLOT_POLICY` needs to be prevented until the next advance call.
*  Set `CONTROL_SHADOWED.OPERATION` to `Advance`.
*  Set `CONTROL_SHADOWED.SLOT_SRC_SEL` to the source slot which acts as the parent in the DICE key hierarchy.
*  Set `CONTROL_SHADOWED.SLOT_DST_SEL` to the destination slot that should store the child key in the DICE hierarchy.
The destination must be same as `SLOT_SRC_SEL`, if `retain_parent = false`.
Otherwise, it must be different.
*  Set `START` to initiate the operation.

Further advance calls use the keys stored in the specified `SLOT_SRC_SEL` slot (whose context is simply referred to as parent), and the result of the derivation updates the slot specified by `SLOT_DST_SEL` (referred to as child).

At the end of a successful operation, the slot selected by `SLOT_DST_SEL` is loaded in with the following values:
*  `valid` bit is set to 1.
*  Its `key_policy` is updated with `SLOT_POLICY`.
*  `max_key_version` is updated with `MAX_KEY_VERSION`.
*  `boot_stage` is set to the parent’s `boot_stage + 1`
*  `key` is updated from the digest received from KMAC (after truncating to 256-bit).

The slot `SLOT_SRC_SEL` remains unmodified (unless `SLOT_SRC_SEL = SLOT_DST_SEL` required by `retain_parent = false`).

A non-successful operation does not update any of the slots.

The software is able to read the current state of key manager, however it never has access to the associated internal key.

## Versioned Key Generation

SW needs to configure the following registers:
*  Set `CONTROL_SHADOWED.DST_SEL` for either of of the use cases {`AES`, `KMAC`, `OTBN`}.
*  Set `CONTROL_SHADOWED.OPERATION` to either of {Generate SW Operation, Generate HW Operation}.
*  Set `CONTROL_SHADOWED.SLOT_SRC_SEL` to select the source slot whose secret will be used to generate the key.
*  Set `SALT` and `KEY_VERSION` registers.
*  Trigger the operation by setting `START`.

If SW key is requested, then it becomes available at `SW_SHARE0_OUTPUT`, `SW_SHARE1_OUTPUT` registers in two shares.
If HW key is requested then it becomes available in the configured sideload port.
The key on the slot remains valid unless:
*  It is explicitly cleared by SW.
*  The same sideload slot or CSR is overwritten by another key generation operation.
*  The keymgr_dpe moves to `Invalid` state.

## Erase Slot

SW needs to configure the following registers to erase a slot:
*  Set `CONTROL_SHADOWED.OPERATION` to `Erase Slot`.
*  Set `CONTROL_SHADOWED.SLOT_DST_SEL` to select the slot to be erased.
*  Set `START` to initiate the operation.

At the end of a successful erase operation, the secret of the destination slot is removed and the slot is marked as invalid.

# Disable

SW needs to configure the following registers to disable keymgr_dpe:
*  Set `CONTROL_SHADOWED.OPERATION` to `Disable`.
*  Set `START` to initiate the operation.

## Caveats
