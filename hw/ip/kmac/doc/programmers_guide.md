# Programmer's Guide

## Initialization

The software can update the KMAC/SHA3 configurations only when the IP is in the idle state.
The software should check [`STATUS.sha3_idle`](registers.md#status) before updating the configurations.
The software must first program [`CFG_SHADOWED.msg_endianness`](registers.md#cfg_shadowed) and [`CFG_SHADOWED.state_endianness`](registers.md#cfg_shadowed) at the initialization stage.
These determine the byte order of incoming messages (msg_endianness) and the Keccak state output (state_endianness).

## Software Initiated KMAC/SHA3 process

This section describes the expected software process to run the KMAC/SHA3 HWIP.
At first, the software configures [`CFG_SHADOWED.kmac_en`](registers.md#cfg_shadowed) for KMAC operation.
If KMAC is enabled, the software should configure [`CFG_SHADOWED.mode`](registers.md#cfg_shadowed) to cSHAKE and [`CFG_SHADOWED.kstrength`](registers.md#cfg_shadowed) to 128 or 256 bit security strength.
If KMAC is enabled, software must also set [`ENTROPY_CFG_SHADOWED.entropy_boot_mode`](registers.md#entropy_cfg_shadowed--entropy_boot_mode) to 0 and it is recommended to enable the EDN Mode (see #edn-entropy-mode for details).
Software must then wait for the [`STATUS.entropy_ready`](registers.md#status--entropy_ready) bit to go high.
The software also updates [`PREFIX`](registers.md#prefix) registers if cSHAKE mode is used.
Current design does not convert cSHAKE mode to SHAKE even if [`PREFIX`](registers.md#prefix) is empty string.
It is the software's responsibility to change the [`CFG_SHADOWED.mode`](registers.md#cfg_shadowed) to SHAKE in case of empty [`PREFIX`](registers.md#prefix).
The KMAC/SHA3 HWIP uses [`PREFIX`](registers.md#prefix) registers as it is.
It means that the software should update [`PREFIX`](registers.md#prefix) with encoded values.

If [`CFG_SHADOWED.kmac_en`](registers.md#cfg_shadowed) is set, the software should update the secret key.
The software prepares two shares of the secret key and selects its length in [`KEY_LEN`](registers.md#key_len) then writes the shares of the secret key to [`KEY_SHARE0`](registers.md#key_share0) and [`KEY_SHARE1`](registers.md#key_share1) .
The two shares of the secret key are the values that represent the secret key value when they are XORed together.
The software can XOR the unmasked secret key with entropy.
The XORed value is a share and the entropy used is the other share.

After configuring, the software notifies the KMAC/SHA3 engine to accept incoming messages by issuing Start command into [`CMD`](registers.md#cmd) .
If Start command is not issued, the incoming message is discarded.
If KMAC is enabled, the software pushes the `right_encode(output_length)` value at the end of the message.
For example, if the desired output length is 256 bit, the software writes `0x00020100` to MSG_FIFO.

After the software pushes all messages, it issues Process command to [`CMD`](registers.md#cmd) for SHA3 engine to complete the sponge absorbing process.
SHA3 hashing engine pads the incoming message as defined in the SHA3 specification.

After the SHA3 engine completes the sponge absorbing step, it generates `kmac_done` interrupt.
Or the software can poll the [`STATUS.squeeze`](registers.md#status) bit until it becomes 1.
In this stage, the software may run the Keccak round manually.

If the desired digest length is greater than the Keccak rate, the software issues Run command for the Keccak round logic to run one full round after the software reads the current available Keccak state.
At this stage, KMAC/SHA3 does not raise an interrupt when the Keccak round completes the software initiated manual run.
The software should check [`STATUS.squeeze`](registers.md#status) register field for the readiness of [`STATE`](registers.md#state) value.

After the software reads all the digest values, it issues Done command to [`CMD`](registers.md#cmd) register to clear the internal states.
Done command clears the Keccak state, FSM in SHA3 and KMAC, and a few internal variables.
Secret key and other software programmed values won't be reset.


## Endianness

This KMAC HWIP operates in little-endian.
Internal SHA3 hashing engine receives in 64-bit granularity.
The data written to SHA3 is assumed to be little endian.

The software may write/read the data in big-endian order if [`CFG_SHADOWED.msg_endianness`](registers.md#cfg_shadowed) or [`CFG_SHADOWED.state_endianness`](registers.md#cfg_shadowed) is set.
If the endianness bit is 1, the data is assumed to be big-endian.
So, the internal logic byte-swap the data.
For example, when the software writes `0xDEADBEEF` with endianness as 1, the logic converts it to `0xEFBEADDE` then writes into MSG_FIFO.

The software managed secret key, and the prefix are always little-endian values.
For example, if the software configures the function name `N` in KMAC operation, it writes `encode_string("KMAC")`.
The `encode_string("KMAC")` represents `0x01 0x20 0x4b 0x4d 0x41 0x43` in byte order.
The software writes `0x4d4b2001` into [`PREFIX0`](registers.md#prefix) and `0x????4341` into [`PREFIX1`](registers.md#prefix) .
Upper 2 bytes can vary depending on the customization input string `S`.


## Entropy Configuration

The internal pseudo-random number generator (PRNG) can be configured in different modes.

## Entropy Boot Mode

This is mode is enabled when the [`ENTROPY_CFG_SHADOWED.entropy_boot_mode`](registers.md#entropy_cfg_shadowed--entropy_boot_mode) bit reads as 0 which is always the case after reset.
The sole purpose of the Entropy Boot Mode is to enable the KMAC HWIP block to perform the [initial ROM integrity check](../../rom_ctrl/doc/theory_of_operation.md#the-startup-rom-check) directly after system reset.

Before the module can operate in KMAC operation, software has to disable the Entropy Boot Mode by setting the [`ENTROPY_CFG_SHADOWED.entropy_boot_mode`](registers.md#entropy_cfg_shadowed--entropy_boot_mode) bit to 0 and enabling either enabling the EDN or Software Entropy Mode using the [`ENTROPY_CFG_SHADOWED.entropy_mode`](registers.md#entropy_cfg_shadowed--entropy_mode) bit.
Once the Entropy Boot Mode is disabled, it cannot be re-enabled again until the next reset.

## EDN Entropy Mode

For regular operation, [`ENTROPY_CFG_SHADOWED.entropy_mode`](registers.md#entropy_cfg_shadowed--entropy_mode) should be set to EDN Mode.
To actually enable this mode, [`ENTROPY_CFG_SHADOWED.entropy_boot_mode`](registers.md#entropy_cfg_shadowed--entropy_boot_mode) needs to read as 0.
In this mode, the module automatically reseeds the internal PRNG with fresh entropy from EDN after every [`ENTROPY_CFG_SHADOWED.edn_mode_refresh_threshold`](registers.md#entropy_cfg_shadowed) key absorption phases in KMAC mode ([`CFG_SHADOWED.kmac_en`](registers.md#cfg_shadowed--kmac_en) set to 1).
Alternatively, software can manually initiate reseeding operations using the [`CMD.entropy_req`](registers.md#cmd--entropy_req) bit while the module is idle.

While previous versions of the OpenTitan KMAC hardware IP block could deadlock the system due to the Message FIFO running full while the KMAC HWIP was waiting for fresh entropy from EDN, this version of the KMAC HWIP is entirely deadlock free.
In particular:
- Irrespective of the configured entropy mode, any operation including KMAC mode operations will finish without blocking the SHA3 engine.
- Even if a PRNG reseed operation is triggered after the key absorption phase in KMAC mode or during the message absorption phase, the PRNG can continue providing randomness to the SHA3 engine.
- This means software can always push data into the Message FIFO.
  In case the Message FIFO is full, software is stalled for at most 100 clock cycles.

The only thing that software needs to ensure before starting an operation in KMAC mode is that the [`STATUS.entropy_ready`](registers.md#status) bit reads as 1, indicating that the previous reseed operation has finished and the PRNG is ready to provide randomness to the SHA3 engine.
If this bit doesn't read as 1 upon starting a KMAC mode operation, a `ErrSwHashingWithoutEntropyReady` error is returned to software, while application interfaces return a service rejected error.

## Software Entropy Mode

As an alternative to the EDN Mode, [`ENTROPY_CFG_SHADOWED.entropy_mode`](registers.md#entropy_cfg_shadowed--entropy_mode) can be set to Software Mode.
To actually enable this mode, [`ENTROPY_CFG_SHADOWED.entropy_boot_mode`](registers.md#entropy_cfg_shadowed--entropy_boot_mode) needs to read as 0.
Software then has wait for the [`STATUS.entropy_reseeding`](registers.md#status--entropy_reseeding) bit to get set to provide an initial seed to the PRNG by writing the [`ENTROPY_SEED`](registers.md#entropy_seed) register 6 times.

Unlike previous versions of the OpenTitan KMAC hardware IP block, this version of the KMAC HWIP allows to move out of the Software Entropy Mode as well as to reseed the PRNG at a later point, unless [the entropy configuration is locked down](#locking-down-the-entropy-configuration).

## Manually triggering PRNG reseeds

If the value of [`ENTROPY_REFRESH_HASH_CNT`](registers.md#entropy_refresh_hash_cnt) gets sufficiently close to what software considers the maximum value, it should:

1. Ensure that the entropy complex is running (only required when running in EDN Mode).
2. Check that the KMAC module is idle by reading the [`STATUS.sha3_idle`](registers.md#status--sha3_idle) bit.
3. Trigger a manual reseed operation by setting the [`CMD.entropy_req`](registers.md#cmd--entropy_req) bit.
4. Wait for the [`STATUS.entropy_reseeding`](registers.md#status--entropy_reseeding) bit to get set.
   Due to the ongoing reseed operation, the [`STATUS.entropy_reseeding`](registers.md#status--entropy_reseeding) bit should remain 1 for an extended period of time.
5. Wait for the [`STATUS.entropy_reseeding`](registers.md#status--entropy_reseeding) bit to get cleared and the [`STATUS.entropy_ready`](registers.md#status--entropy_ready) bit to get set when running in EDN Mode.
   When running in Software Mode, provide 6 times 32 bits of entropy via the [`ENTROPY_SEED`](registers.md#entropy_seed) register.
   After the last write operation the [`STATUS.entropy_ready`](registers.md#status--entropy_ready) bit will get set back to 1.

The [`ENTROPY_REFRESH_HASH_CNT`](registers.md#entropy_refresh_hash_cnt) register should now read as 0.

## Locking down the Entropy Configuration

In some cases, it may be desirable for software to lock down the entropy configuration and even prevent further reseed operations, e.g., if later software stages aren't trusted.
To lock the entropy configuration, software should:

1. Ensure the proper configuration is set in  [`ENTROPY_CFG_SHADOWED`](registers.md#entropy_cfg_shadowed).
   In particular, if software wants to prevent further reseed operations, [`ENTROPY_CFG_SHADOWED.edn_mode_refresh_threshold`](registers.md#entropy_cfg_shadowed--edn_mode_refresh_threshold) must be set to 0 to disable automatic reseed operations in EDN Mode and [`ENTROPY_CFG_SHADOWED.ignore_cmd_entropy_req`](registers.md#entropy_cfg_shadowed--ignore_cmd_entropy_req) must be set to 0 to ignore manual reseed requests in both EDN and Software Mode.
2. Set the [`ENTROPY_CFG_LOCK`](registers.md#entropy_cfg_lock) register to 1.

After that point, the entropy configuration is locked until the next reset. 

## Error Handling

When the KMAC HW IP encounters an error, it raises the `kmac_err` IRQ.
SW can then read the `ERR_CODE` CSR to obtain more information about the error.
Having handled that IRQ, SW is expected to clear the `kmac_err` bit in the `INTR_STATE` CSR before exiting the ISR.
When SW has handled the error condition, it is expected to set the `err_processed` bit in the `CMD` CSR.
The internal SHA3 engine then flushes its FIFOs and state, which may take a few cycles.
The KMAC HW IP is ready for operation again as soon as the `sha3_idle` bit in the `STATUS` CSR is set; SW must not change the configuration of or send commands to the KMAC HW IP before that.
If the error occurred while the KMAC HW IP was being used from SW (i.e., not via an HW application interface), the `kmac_done` IRQ is raised when the KMAC HW IP is ready again.


## KMAC/SHA3 context switching

This version of KMAC/SHA3 HWIP does support context switching enabling software to save the current hashing engine state and initiate a new high priority hashing operation.
The IP enables software to restore the previous hashing state later and continue the operation.

Context switching is supported for all hashing modes.

### The context

The context is the internal Keccak state that is exposed over [`STATE`](registers.md#state).
Software must keep this state secret as computing back to the used key is possible.
If `EnMasking` is enabled, the state is kept in two shares and both of them are part of the context.
Software does not need to unmask the state, saving and restoring both shares as they are is sufficient.
If `EnMasking` is disabled, the second share reads as zero and writes to it are ignored.

The secret key is _not_ directly part of the context.
It has been absorbed into the Keccak state when the operation was started, so the [`KEY_SHARE0`](registers.md#key_share0) and [`KEY_SHARE1`](registers.md#key_share1) registers do not need to be restored.
Software must, however, restore [`CFG_SHADOWED`](registers.md#cfg_shadowed) to the value that was used when the context was saved.
[`CFG_SHADOWED.kstrength`](registers.md#cfg_shadowed) determines the block size of the remaining message and [`CFG_SHADOWED.mode`](registers.md#cfg_shadowed) the padding that terminates the operation.

### Message block alignment

Saving a context is only possible in the absorb phase at the boundary of complete message blocks.
A message block is complete when the message written since the last Start or Continue command is a multiple of the Keccak rate.
The Keccak rate depends on the configured mode and security strength:

| [`CFG_SHADOWED.mode`](registers.md#cfg_shadowed) | [`CFG_SHADOWED.kstrength`](registers.md#cfg_shadowed) | Block size |
|---------------|-----|-----------|
| SHA3          | 224 | 144 bytes |
| SHA3          | 256 | 136 bytes |
| SHA3          | 384 | 104 bytes |
| SHA3          | 512 | 72 bytes  |
| SHAKE, cSHAKE | 128 | 168 bytes |
| SHAKE, cSHAKE | 256 | 136 bytes |

Bytes that have been written but not yet absorbed are not part of the Keccak state and can therefore not be saved.
If software issues the `stop` command in this situation, `ErrSwStopNotBlockAligned` is reported, see [Saving a context](#saving-a-context).

### Saving a context

To save a context, software needs to follow this procedure:
1. Write the `stop` command into [`CMD`](registers.md#cmd).
1. Poll [`STATUS.sha3_stopped`](registers.md#status--sha3_stopped) or wait for the `kmac_done` interrupt.
1. Read [`STATE`](registers.md#state).
1. Write the `done` command into [`CMD`](registers.md#cmd).

The last step clears the Keccak state.
It prevents the context of one message stream from leaking into another one and it returns the engine into the idle state, which is required before a context can be restored.

If the message is not block aligned when the `stop` command is issued, `ErrSwStopNotBlockAligned` is reported and the absorbed data of the incomplete block is discarded.
The KMAC HWIP still enters the stopped state, so software releases it with the `done` command and starts the message from the beginning.
No other command is accepted in that state.

### Restoring a context

To resume a previously saved context, KMAC HWIP must be idle, and software needs to follow this procedure:
1. Restore [`CFG_SHADOWED`](registers.md#cfg_shadowed) to the configuration that was used when the context was saved.
1. In KMAC mode with masking enabled, ensure the entropy is configured by setting [`ENTROPY_CFG_SHADOWED.entropy_boot_mode`](registers.md#entropy_cfg_shadowed--entropy_boot_mode) to 0 and [`ENTROPY_CFG_SHADOWED.entropy_mode`](registers.md#entropy_cfg_shadowed--entropymode), as for the `start` command.
   Otherwise, the `continue` command is discarded and `ErrSwHashingWithoutEntropyReady` is reported.
1. Wait for the [`STATUS.entropy_ready`](registers.md#status--entropy_ready) bit to be set.
1. Write the `state_write` command into [`CMD`](registers.md#cmd).
1. Poll [`STATUS.state_write`](registers.md#status--state_write) until it is set, or until the `kmac_err` interrupt is raised (see below).
1. Write the saved context back into [`STATE`](registers.md#state).
1. Write the `continue` command into [`CMD`](registers.md#cmd).

The `state_write` command claims the KMAC/SHA3 HWIP for software, preventing that an application interface takes the block over during the restore and clears the Keccak state.
Hence, writes to the [`STATE`](registers.md#state) register are only accepted when the IP block was claimed using this command.
The command also clears the Keccak state itself, so a restore always starts from a known state and the `continue` command resumes only the context written after the claim.

When the application interface already claims the HWIP block, or claims it at the same time, the `state_write` command is discarded and [`ERR_CODE`](registers.md#err_code) reports `ErrSwIssuedCmdInAppActive`.
[`STATUS.state_write`](registers.md#status--state_write) is then never set, so software must not poll it without also checking for this error, as it would otherwise deadlock.
On this error, software waits until the application interface has finished its operation and issues the `state_write` command again.

If software decides not to resume a context after claiming the block, it can release the HWIP with the `done` command.
As after a completed operation, the `done` command clears the Keccak state.

In contrast to the `start` command, the `continue` command does not process the prefix and the secret key block again, as both are already part of the restored context.
Afterwards software writes further message blocks and either saves the context again, or finalizes the operation with the `process` command as described in [Software Initiated KMAC/SHA3 process](#software-initiated-kmacsha3-process).
The final message block does not need to be complete.

### Restrictions

Context switching is not available when a sideloaded key is used.
The Keccak function is public and invertible, so software can undo the absorb of every message block it wrote itself, one inversion per block, until it reaches the state after the secret key and recovers a key it is not supposed to know.
Saving later in the message does not help, as every state in the absorbing stage leads back to the key.
The `stop`, `state_write`, and `continue` commands are discarded while [`CFG_SHADOWED.sideload`](registers.md#cfg_shadowed) is set.

Requests from the hardware application interfaces are stalled while software holds the block through the `state_write` command, until it issues the `done` command.
The `continue` command does not release it.
Software must therefore also issue `done` on its error paths.

The following errors are reported in [`ERR_CODE`](registers.md#err_code) if the procedures above are not followed:

| Error | Description |
|-------|-------------|
| `ErrSwStopNotBlockAligned` | The `stop` command was issued but the message is not a multiple of the block size. The absorb is ended anyway and the incomplete block is discarded, so the operation cannot be resumed and has to be started again. |
| `ErrSwSaveRestoreSideload` | The `stop`, `state_write` or `continue` command was issued while a sideloaded key is selected. |
| `ErrSwIssuedCmdInAppActive` | A command, for example `state_write`, was issued while a hardware application interface was using the block. |
| `ErrSwCmdSequence` | A command was issued that is not allowed in the current state, e.g. `run` after the `stop` command, or `continue` without a preceding `state_write` command. |
| `ErrSwHashingWithoutEntropyReady` | The `continue` command was issued in KMAC mode while masking is enabled, but the PRNG is not ready and needs to be reseeded. As for the `start` command, the command is discarded. |

## Device Interface Functions (DIFs)

- [Device Interface Functions](../../../../sw/device/lib/dif/dif_kmac.h)
