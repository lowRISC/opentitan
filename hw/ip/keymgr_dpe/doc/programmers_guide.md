# Programmer's Guide

Before initiating any of the following key generation operations, it is recommended (but not mandatory) to check that keymgr_dpe is ready to handle them.
Except for the first advance call that initializes keymgr_dpe, this means keymgr_dpe is idle (as reported in `OP_STATUS`) and FSM is in `Available` state (reported in `WORKING_STATE`).

Similarly, at the end of the operation (when `OP_STATUS` is not `WIP` anymore), it is recommended to check that the operation was successful by reading `ERR_CODE`.
SW can also read the reported FSM state through `WORKING_STATE` to confirm that keymgr_dpe reaches the expected state.

## Initialize (first advance call)

From a SW perspective, there is not an explicit initialize command.
Initialization is simply the first advance call.
The first advance call only latches the OTP root key, therefore most registers used in the regular advance call are ignored during initialization.

Keymgr_dpe is initialized by configuring the following CSR:
*  Set `CONTROL_SHADOWED.OPERATION` to `Advance`.
*  Set `CONTROL_SHADOWED.SLOT_DST_SEL` to select which slot UDS should be latched to.
*  Set `START` to initiate the operation.

At the end of the successful first advance call, the UDS is latched into the specified destination slot.

## Advance

This section specifically addresses the advance calls after initialization (i.e. the first advance call).
The advance operation is executed by configuring the following CSR:

*  Set `SW_CDI_INPUT`.
*  Set `SW_BINDING_REGWEN` to lock `SW_CDI_INPUT`, if modifications on `SW_CDI_INPUT` needs to be prevented until the next advance call.
*  Set `MAX_KEY_VERSION`.
*  Write `MAX_KEY_REGWEN` with zero to lock `MAX_KEY_VERSION`, if modifications on `MAX_KEY_VERSION` needs to be prevented until the next advance call.
*  Set `CONTROL_SHADOWED.OPERATION` to `Advance`.
*  Set `CONTROL_SHADOWED.SLOT_SRC_SEL` to select the source slot which acts as the parent in the DICE key hierarchy.
*  Set `CONTROL_SHADOWED.SLOT_DST_SEL` to select where the resulting secret of the child key in the DICE hierarchy be written.
*  Set `SLOT_POLICY` to control policy fields of the generated child slot.
*  Set `START` to initiate the operation.

Further advance calls use the keys stored in the specified SLOT_SRC_SEL slot (whose context is simply referred to as parent) , and the result of the derivation updates the slot specified by SLOT_DST_SEL (referred to as child).

At the end of a successful operation, the slot selected by SLOT_DST_SEL is loaded in with the following values:
*  valid bit is set to 1,
*  its key_policy is updated (based on the parent’s policy and SLOT_POLICY)
*  max_key_version is updated with MAX_KEY_VERSION register,
*  boot_stage is set to the parent’s boot_stage + 1,
key is updated from the key received from KMAC.
The slot SLOT_SRC_SEL remains unmodified (unless SLOT_SRC_SEL = SLOT_DST_SEL).

A non-successful operation does not update any of the slots.

The software is able to read the current state of key manager, however it never has access to the associated internal key.

## Versioned Key Generation

SW needs to configure the following registers:
*  Set `CONTROL_SHADOWED.DST_SEL` for either of of the use cases {AES, KMAC, OTBN}.
*  Set `CONTROL_SHADOWED.OPERATION` to either of {Generate SW Operation, Generate HW Operation}.
*  Set `CONTROL_SHADOWED.SLOT_SRC_SEL` to select the source slot whose secret will be used to generate the key.
*  Set `SALT and KEY_VERSION` registers.
*  Trigger the operation by setting START.

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
