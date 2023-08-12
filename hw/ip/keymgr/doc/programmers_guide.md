# Programmer's Guide

## Initialize

## Advance or Generate
Software selects a command and triggers a "start".
If the command is valid and successful, key manager indicates done and no errors.
If the command is invalid or unsuccessful, key manager indicates done with error.
Regardless of the validity of the command, the hardware sequences are triggered to avoid leaking timing information.

The software is able to read the current state of key manager, however it never has access to the associated internal key.

When issuing the `generate-output-hw` command, software must select a destination primitive (AES, KMAC or OTBN).
At the conclusion of the command, key and valid signals are forwarded by the key manager to the selected destination primitive.
The key and valid signals remain asserted to the selected destination until software explicitly disables the output via another command, or issues another `generate-output-hw` command with a different destination primitive.

## Caveats
The keymgr [`WORKING_STATE`](registers.md#working_state) register allows software to discover the current state of `keymgr`.
However, since these values are not hardened, they can be attacked.
As such, software should be careful to not make critical system decisions based on these registers.
They are meant generally for informational or debug purposes.

## Device Interface Functions (DIFs)

- [Device Interface Functions](../../../../sw/device/lib/dif/dif_keymgr.h)
