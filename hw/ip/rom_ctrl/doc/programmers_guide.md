# Programmer's Guide

Software will mostly interact with the ROM controller by fetching code or loading data from ROM.
For this, the block looks like a block of memory, accessible through a TL-UL window.
However, there are a few registers that are accessible.
Other than the standard [`ALERT_TEST`](registers.md#alert_test) register, all are read-only.

The [`FATAL_ALERT_CAUSE`](registers.md#fatal_alert_cause) register might change value during operations (if an alert is signalled), but the other registers will all have fixed values by the time any software runs.

To get the computed ROM digest, software can read [`DIGEST_0`](registers.md#digest) through [`DIGEST_7`](registers.md#digest).
The ROM also contains an expected ROM digest.
Unlike the rest of the contents of ROM, this isn't scrambled.
As such, software can't read it through the standard ROM interface (which would try to unscramble it again, resulting in rubbish data that would cause a failed ECC check).
In case software needs access to this value, it can be read at [`EXP_DIGEST_0`](registers.md#exp_digest) through [`EXP_DIGEST_7`](registers.md#exp_digest).

## Device Interface Functions (DIFs)

- [Device Interface Functions](../../../../sw/device/lib/dif/dif_rom_ctrl.h)
