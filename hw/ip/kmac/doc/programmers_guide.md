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


## EDN Entropy Mode

For regular operation, [`CFG_SHADOWED.entropy_mode`](registers.md#cfg_shadowed--entropy_mode) should be set to EDN mode.
In this mode, the module automatically reseeds the internal PRNG with fresh entropy from EDN after every [`ENTROPY_REFRESH_THRESHOLD_SHADOWED`](registers.md#entropy_refresh_threshold_shadowed) key absorption phases in KMAC mode.
Alternatively, software can manually initiate reseeding operations using the [`CMD.entropy_req`](registers.md#cmd--entropy_req) bit while the module is idle.


### Preventing potential deadlocks in EDN mode

Under normal operating conditions, the SHA3 engine will process data a lot faster than software can push it to the Message FIFO.
However, the Message FIFO may run full while the SHA3 engine is busy.
In particular, this might happen because KMAC is waiting for fresh entropy from EDN.
If software then tries to push further data to the Message FIFO, the processor will get stalled and if the entropy is not delivered (on time), the system may deadlock (see [Empty and Full status](theory_of_operation.md#empty-and-full-status) for details).

To avoid this deadlock scenario, software should either:
- Manually trigger PRNG reseed operations after ensuring the entropy complex is up and running (recommended), or
- Check the Message FIFO depth before pushing data.

Since the latter option can be inconvenient for software, especially when processing long messages, manually triggering PRNG reseed operations is the recommended approach.
In the following, both approaches are outlined in more detail.


#### Manually triggering PRNG reseeds

Since automatic reseeds of the internal PRNG are always triggered after the key absorption phase in KMAC mode ([`CFG_SHADOWED.kmac_en`](registers.md#cfg_shadowed--kmac_en) set to 1), and since every message in KMAC mode has only one such phase, it is sufficient for software to check the [`ENTROPY_REFRESH_HASH_CNT`](registers.md#entropy_refresh_hash_cnt) register after finishing a KMAC message.

If the value of [`ENTROPY_REFRESH_HASH_CNT`](registers.md#entropy_refresh_hash_cnt) gets sufficiently close to the value of [`ENTROPY_REFRESH_THRESHOLD_SHADOWED`](registers.md#entropy_refresh_threshold_shadowed), software should:

1. Ensure that the entropy complex is running.
2. Check that the KMAC module is idle by reading the [`STATUS.sha3_idle`](registers.md#status--sha3_idle) bit.
3. Trigger a manual reseed operation by setting the [`CMD.entropy_req`](registers.md#cmd--entropy_req) bit.
4. Configure the module to process a message in cSHAKE mode (but not in KMAC mode).
   More precisely, set [`CFG_SHADOWED.mode`](registers.md#cfg_shadowed--mode) to `0x3` and [`CFG_SHADOWED.kmac_en`](registers.md#cfg_shadowed--kmac_en) to 0.
5. Configure the module to use the PRNG and block any hashing operation if the PRNG is not ready by setting [`CFG_SHADOWED.entropy_fast_process`](registers.md#cfg_shadowed--entropy_fast_process) to 0.
6. Send the `start` command to the [`CMD`](registers.md#cmd) register.
   The SHA3 engine will start loading and hashing the function name `N` and the customization string `S` first.
7. Send the `process` command to the [`CMD`](registers.md#cmd) register.
8. Wait for the [`STATUS.sha3_squeeze`](registers.md#status--sha3_squeeze) bit to get set.
   Due to the ongoing reseed operation, the [`STATUS.sha3_squeeze`](registers.md#status--sha3_squeeze) bit should remain 0 for an extended period of time.
9. Send the `done` command to the [`CMD`](registers.md#cmd) register to finish processing.

The [`ENTROPY_REFRESH_HASH_CNT`](registers.md#entropy_refresh_hash_cnt) register should now read as 0.
Note however that if the manual reseed operation is triggered while the KMAC module is busy, the reseed operation may get skipped despite the hash counter being cleared back to 0.


#### Checking Message FIFO depth before pushing data

Alternatively, software can avoid ever pushing data into the Message FIFO while the FIFO is full by regularly checking the FIFO depth.
In particular, software can then:

1. Check the FIFO depth [`STATUS.fifo_depth`](registers.md#status--fifo_depth).
   This represents the number of entry slots currently occupied in the FIFO.
2. Calculate the remaining size as (`<max number of FIFO entries> - <STATUS.fifo_depth>) * <entry size>`.
3. Write data to fill at most the calculated remaining size.
4. Repeat until all data is written.
   In case the FIFO runs full (check [`STATUS.fifo_full`](registers.md#status--fifo_full)), software should check the entropy complex is running and can then optionally wait for the `fifo_empty` status interrupt before continuing.

In code, this looks something like:
```c
/**
 * Absorb input data into the Keccak computation.
 *
 * Assumes that the KMAC block is in the "absorb" state; it is the caller's
 * responsibility to check before calling.
 *
 * @param in Input buffer.
 * @param in_len Length of input buffer (bytes).
 * @return Number of bytes written.
 */
size_t kmac_absorb(const uint8_t *in, size_t in_len) {
    // Read FIFO depth from the status register.
    uint32_t status = abs_mmio_read32(kBase + KMAC_STATUS_REG_OFFSET);
    uint32_t fifo_depth =
        bitfield_field32_read(status, KMAC_STATUS_FIFO_DEPTH_FIELD);

    // Calculate the remaining space in the FIFO using auto-generated KMAC
    // parameters and take the minimum of that space and the input length.
    size_t free_entries = (KMAC_PARAM_NUM_ENTRIES_MSG_FIFO - fifo_depth);
    size_t max_len = free_entries * KMAC_PARAM_NUM_BYTES_MSG_FIFO_ENTRY;
    size_t write_len = (in_len < max_len) ? in_len : max_len;

    // Note: this example uses byte-writes for simplicity, but in practice it
    // would be more efficient to use word-writes for aligned full words and
    // byte-writes only as needed at the beginning and end of the input.
    for (size_t i = 0; i < write_len; i++) {
      abs_mmio_write8(kBase + KMAC_MSG_FIFO_REG_OFFSET, in[i]);
    }

    return write_len;
}
```

Note that for modes other than KMAC, i.e., if [`CFG_SHADOWED.kmac_en`](registers.md#cfg_shadowed--kmac_en) is 0, the KMAC module will not increment the [`ENTROPY_REFRESH_HASH_CNT`](registers.md#entropy_refresh_hash_cnt) register and thus not trigger automatic reseeds.
It is safe to push to the Message FIFO without checking the [`STATUS.fifo_depth`](registers.md#status--fifo_depth) register.


### Configuring ENTROPY_PERIOD

The [`ENTROPY_PERIOD`](registers.md#entropy_period) register defines how long the module should wait for entropy during a PRNG reseed before triggering an error.
The configuration value should be carefully chosen based on how the entropy complex is operated.

If CSRNG is running in [fully deterministic mode](../../csrng/doc/programmers_guide.md#fully-deterministic-mode), any EDN request will be answered fairly quickly.
An [`ENTROPY_PERIOD.wait_timer`](registers.md#entropy_period--wait_timer) value of 5000 in combination with an [`ENTROPY_PERIOD.prescaler`](registers.md#entropy_period--prescaler) value of 0 is adequate.

If CSRNG is running in [regular, non-deterministic mode](../../csrng/doc/programmers_guide.md#regular-non-deterministic-mode), it can happen that the PRNG reseed request of the KMAC module triggers a reseed request from EDN0 to CSRNG.
For [Top Earlgrey](../../../top_earlgrey/README.md), producing a single CSRNG seed value is expected to take roughly 5ms.
In the worst case, ENTROPY_SRC must first generate two more seeds to reseed all the other two CSRNG instances.
In this case, the PRNG reseed request of KMAC should get served after roughly 15ms.
If the ENTROPY_SRC is disabled, the interrupt latency and the delay for the startup health testing of the ENTROPY_SRC also need to be factored in to define the [`ENTROPY_PERIOD`](registers.md#entropy_period) configuration value.


### Leaving EDN mode

If the entropy complex becomes unavailable, software can cause the module to leave EDN mode as follows.
Note that for this to work reliably, it is recommended to configure the [`ENTROPY_PERIOD`](registers.md#entropy_period) register to a non-zero value (see [`Configuring ENTROPY_PERIOD`](#configuring-entropy_period)).
Otherwise, an already ongoing reseed operation may prevent the following procedure from working.

1. Configure the [`ENTROPY_PERIOD`](registers.md#entropy_period) to a sufficiently small value such as `wait_timer` equals 1 and `prescaler` equals 0, or disable EDN0 which interfaces KMAC.
2. Check that the KMAC module is idle by reading the [`STATUS.sha3_idle`](registers.md#status--sha3_idle) bit.
3. Trigger a PRNG reseed operation via the [`CMD.entropy_req`](registers.md#cmd--entropy_req) bit.
4. Wait for the entropy request to timeout and the `kmac_err` interrupt to fire.
   The [`ERR_CODE`](registers.md#err_code) should now read `ErrWaitTimerExpired`.
5. De-assert the [`CFG_SHADOWED.entropy_ready`](registers.md#cfg_shadowed--entropy_ready) bit.
6. Set the [`CMD.err_processed`](registers.md#cmd--err_processed) bit to signal the processing of the error condition (see also [Error Handling](#error-handling)).

The FSM controlling the PRNG then goes back into its reset state and software can re-configure the desired mode in the [`CFG_SHADOWED.entropy_mode`](registers.md#cfg_shadowed--entropy_mode) field and set the [`CFG_SHADOWED.entropy_ready`](registers.md#cfg_shadowed--entropy_ready) bit afterwards to latch the configuration.


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
1. Write the `state_write` command into [`CMD`](registers.md#cmd).
1. Poll [`STATUS.state_write`](registers.md#status--state_write).
1. Write the saved context back into [`STATE`](registers.md#state).
1. Write the `continue` command into [`CMD`](registers.md#cmd).

The `state_write` command claims the KMAC/SHA3 HWIP for software, preventing that an application interface takes the block over during the restore and clears the Keccak state.
Hence, writes to the [`STATE`](registers.md#state) register are only accepted when the IP block was claimed using this command.
The command also clears the Keccak state itself, so a restore always starts from a known state and the `continue` command resumes only the context written after the claim.

When the application interface already claims the HWIP block, [`ERR_CODE`](registers.md#err_code) reports `ErrSwIssuedCmdInAppActive`.

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

## Device Interface Functions (DIFs)

- [Device Interface Functions](../../../../sw/device/lib/dif/dif_kmac.h)
