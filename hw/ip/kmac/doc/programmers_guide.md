# Programmer's Guide

## Initialization

The software can update the KMAC/SHA3 configurations only when the IP is in the idle state.
The software should check [`STATUS.sha3_idle`](../data/kmac.hjson#status) before updating the configurations.
The software must first program [`CFG_SHADOWED.msg_endianness`](../data/kmac.hjson#cfg_shadowed) and [`CFG_SHADOWED.state_endianness`](../data/kmac.hjson#cfg_shadowed) at the initialization stage.
These determine the byte order of incoming messages (msg_endianness) and the Keccak state output (state_endianness).

## Software Initiated KMAC/SHA3 process

This section describes the expected software process to run the KMAC/SHA3 HWIP.
At first, the software configures [`CFG_SHADOWED.kmac_en`](../data/kmac.hjson#cfg_shadowed) for KMAC operation.
If KMAC is enabled, the software should configure [`CFG_SHADOWED.mode`](../data/kmac.hjson#cfg_shadowed) to cSHAKE and [`CFG_SHADOWED.kstrength`](../data/kmac.hjson#cfg_shadowed) to 128 or 256 bit security strength.
The software also updates [`PREFIX`](../data/kmac.hjson#prefix_0) registers if cSHAKE mode is used.
Current design does not convert cSHAKE mode to SHAKE even if [`PREFIX`](../data/kmac.hjson#prefix_0) is empty string.
It is the software's responsibility to change the [`CFG_SHADOWED.mode`](../data/kmac.hjson#cfg_shadowed) to SHAKE in case of empty [`PREFIX`](../data/kmac.hjson#prefix_0).
The KMAC/SHA3 HWIP uses [`PREFIX`](../data/kmac.hjson#prefix_0) registers as it is.
It means that the software should update [`PREFIX`](../data/kmac.hjson#prefix_0) with encoded values.

If [`CFG_SHADOWED.kmac_en`](../data/kmac.hjson#cfg_shadowed) is set, the software should update the secret key.
The software prepares two shares of the secret key and selects its length in [`KEY_LEN`](../data/kmac.hjson#key_len) then writes the shares of the secret key to [`KEY_SHARE0`](../data/kmac.hjson#key_share0_0) and [`KEY_SHARE1`](../data/kmac.hjson#key_share1_0) .
The two shares of the secret key are the values that represent the secret key value when they are XORed together.
The software can XOR the unmasked secret key with entropy.
The XORed value is a share and the entropy used is the other share.

After configuring, the software notifies the KMAC/SHA3 engine to accept incoming messages by issuing Start command into [`CMD`](../data/kmac.hjson#cmd) .
If Start command is not issued, the incoming message is discarded.
If KMAC is enabled, the software pushes the `right_encode(output_length)` value at the end of the message.
For example, if the desired output length is 256 bit, the software writes `0x00020100` to MSG_FIFO.

After the software pushes all messages, it issues Process command to [`CMD`](../data/kmac.hjson#cmd) for SHA3 engine to complete the sponge absorbing process.
SHA3 hashing engine pads the incoming message as defined in the SHA3 specification.

After the SHA3 engine completes the sponge absorbing step, it generates `kmac_done` interrupt.
Or the software can poll the [`STATUS.squeeze`](../data/kmac.hjson#status) bit until it becomes 1.
In this stage, the software may run the Keccak round manually.

If the desired digest length is greater than the Keccak rate, the software issues Run command for the Keccak round logic to run one full round after the software reads the current available Keccak state.
At this stage, KMAC/SHA3 does not raise an interrupt when the Keccak round completes the software initiated manual run.
The software should check [`STATUS.squeeze`](../data/kmac.hjson#status) register field for the readiness of [`STATE`](../data/kmac.hjson#state) value.

After the software reads all the digest values, it issues Done command to [`CMD`](../data/kmac.hjson#cmd) register to clear the internal states.
Done command clears the Keccak state, FSM in SHA3 and KMAC, and a few internal variables.
Secret key and other software programmed values won't be reset.


## Endianness

This KMAC HWIP operates in little-endian.
Internal SHA3 hashing engine receives in 64-bit granularity.
The data written to SHA3 is assumed to be little endian.

The software may write/read the data in big-endian order if [`CFG_SHADOWED.msg_endianness`](../data/kmac.hjson#cfg_shadowed) or [`CFG_SHADOWED.state_endianness`](../data/kmac.hjson#cfg_shadowed) is set.
If the endianness bit is 1, the data is assumed to be big-endian.
So, the internal logic byte-swap the data.
For example, when the software writes `0xDEADBEEF` with endianness as 1, the logic converts it to `0xEFBEADDE` then writes into MSG_FIFO.

The software managed secret key, and the prefix are always little-endian values.
For example, if the software configures the function name `N` in KMAC operation, it writes `encode_string("KMAC")`.
The `encode_string("KMAC")` represents `0x01 0x20 0x4b 0x4d 0x41 0x43` in byte order.
The software writes `0x4d4b2001` into [`PREFIX0`](../data/kmac.hjson#prefix_0) and `0x????4341` into [`PREFIX1`](../data/kmac.hjson#prefix_1) .
Upper 2 bytes can vary depending on the customization input string `S`.

## KMAC/SHA3 context switching

This version of KMAC/SHA3 HWIP _does not_ support the software context switching.
A context switching scheme would allow software to save the current hashing engine state and initiate a new high priority hashing operation.
It could restore the previous hashing state later and continue the operation.

## Device Interface Functions (DIFs)

- [Device Interface Functions](../../../../sw/device/lib/dif/dif_kmac.h)

## Registers

* [Register Table](../data/kmac.hjson#registers)

[SHA3 specification, FIPS 202]: https://csrc.nist.gov/publications/detail/fips/202/final
[NIST SP 800-185]: https://csrc.nist.gov/publications/detail/sp/800-185/final
[Domain-Oriented Masking (DOM)]: https://eprint.iacr.org/2017/395.pdf
