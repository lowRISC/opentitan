# Programmer's Guide

This chapter shows how to use the HMAC/SHA-2 IP by showing some snippets such as initialization, initiating SHA-2 or HMAC process and processing the interrupts.
This code is not compilable but serves to demonstrate the IO required.
A more detailed SW implementation can be found in software under `sw/` in [cryptolib code](../../../../sw/device/lib/crypto/drivers/hmac.c) which is the recommended reference implementation for further SW development.
HMAC/SHA-2 IP is also used in [ROM code](../../../../sw/device/silicon_creator/lib/drivers/hmac.c) but this is a constrained implementation for specific ROM code purposes. Therefore, it is not a recommended software implementation reference.
Code in [HMAC DIF](../../../../sw/device/lib/dif/dif_hmac.c) is intended for tesing development purposes, but remains limited to configuring HMAC only in SHA-2 256 with 256-bit key, with plans to update it in the near future.

## Initialization

This section of the code describes initializing the HMAC with SHA-2 256 digest using a 256-bit key: setting up the interrupts, endianness, and HMAC/SHA-2 mode.
[`CFG.endian_swap`](registers.md#cfg) reverses the byte-order of input words when software writes into the message FIFO.
[`CFG.digest_swap`](registers.md#cfg) reverses the byte-order in the final HMAC or SHA hash.

```c
void hmac_init(unsigned int endianess, unsigned int digest_endian) {
  HMAC_CFG(0) = HMAC_CFG_SHA_EN
              | HMAC_CFG_HMAC_EN
              | (endianess << HMAC_CFG_ENDIAN_SWAP_LSB)
              | (digest_endian << HMAC_CFG_DIGEST_SWAP_LSB)
              | (HMAC_CFG_DIGEST_SIZE_FIELD << HMAC_CFG_DIGEST_SIZE_VALUE_SHA2_256)
              | (HMAC_CFG_KEY_LENGTH_FIELD << HMAC_CFG_KEY_LENGTH_FIELD);

  // Enable interrupts if needed.

  // If secret key is static, you can put the key here
  HMAC_KEY_0 = SECRET_KEY_0;
  HMAC_KEY_1 = SECRET_KEY_1;
  HMAC_KEY_2 = SECRET_KEY_2;
  HMAC_KEY_3 = SECRET_KEY_3;
  HMAC_KEY_4 = SECRET_KEY_4;
  HMAC_KEY_5 = SECRET_KEY_5;
  HMAC_KEY_6 = SECRET_KEY_6;
  HMAC_KEY_7 = SECRET_KEY_7;
}
```

## Triggering HMAC/SHA-2 engine

The following code shows how to send a message to the HMAC, the procedure is the same whether a full HMAC or just a SHA-2 computation is required (choose between them using [`CFG.hmac_en`](registers.md#cfg)).
In both cases the SHA-2 engine must be enabled using [`CFG.sha_en`](registers.md#cfg) (once all other configuration inputs have been properly set).
If the message is larger than 512-bit, the software must wait until the FIFO is not full before writing further bits.
For SHA-2 256, only `DIGEST_0`..`7` should be read out, the remaining digest registers are redundant and would hold irrelevant values.
For SHA-2 384, only `DIGEST_0`..`11` should be read out, the rest should be truncated out by not being read by the SW.
For SHA-2 512, all `DIGEST_0`..`15` should be read out.

```c
void run_hmac(uint32_t *msg, uint32_t msg_len, uint32_t *hash) {
  // Initiate hash: hash_start
  REG32(HMAC_CMD(0)) = (1 << HMAC_CMD_HASH_START);

  // write the message: below example assumes word-aligned access
  for (uint32_t written = 0 ; written < (msg_len >> 3) ; written += 4) {
    while((REG32(HMAC_STATUS(0)) >> HMAC_STATUS_FIFO_FULL) & 0x1) ;
    // Any write data from HMAC_MSG_FIFO_OFFSET to HMAC_MSG_FIFO_SIZE
    // is written to the message FIFO
    REG32(HMAC_MSG_FIFO(0)) = *(msg+(written/4));
  }

  // Completes hash: hash_process
  REG32(HMAC_CMD(0)) = (1 << HMAC_CMD_HASH_PROCESS);

  while(0 == (REG32(HMAC_INTR_STATE(0)) >> HMAC_INTR_STATE_HMAC_DONE) & 0x1);

  REG32(HMAC_INTR_STATE(0)) = 1 << HMAC_INTR_STATE_HMAC_DONE;

  // Read the digest
  for (int i = 0 ; i < 8 ; i++) {
    *(hash + i) = REG32(HMAC_DIGEST_0(0) + (i << 2));
  }
}
```

## Updating the configurations

The HMAC IP prevents [`CFG`](registers.md#cfg) and [`KEY`](registers.md#key) registers from getting updating while the engine is processing messages.
Such attempts are discarded.
The [`KEY`](registers.md#key) register ignores any attempt to access the secret key in the middle of the process.
If the software tries to update the KEY, the IP reports an error through the [`ERR_CODE`](registers.md#err_code) register.
The error code is `SwUpdateSecretKeyInProcess`, `0x0003`.

## Saving and restoring the context

Software can let the HMAC IP process multiple message streams in a time-interleaved fashion by saving and restoring the context (i.e., parts of the hardware-internal state).

Such context switches are possible only at the boundary of complete message blocks (512-bit for SHA-2 256 or 1024-bit for SHA-2 384/512).
When SW doesn't know each instant at which a full message block is available, it can buffer data in memory until a block is full and only write HMAC's FIFOs once the buffer in memory contains a full message block.

The context that needs to be saved and restored is in the following registers: [`CFG`](registers.md#cfg), [`DIGEST_*`](registers.md#digest), and [`MSG_LENGTH_*`](registers.md#msg_length_lower).

Each new message stream needs to be started *once* by setting the `CMD.hash_start` bit and finalized *once* by setting the `CMD.hash_process` bit.
To switch from one message stream to another, set the `CMD.hash_stop` bit, wait for the `hmac_done` interrupt (or status bit), save one context and restore the other, and then set the `CMD.hash_continue` bit.

Here is an example usage pattern of this feature:
1. Start processing message stream A by configuring HMAC and then setting the `CMD.hash_start` bit.
1. Write an arbitrary number of message blocks to HMAC's `MSG_FIFO`.
1. Stop HMAC by setting the `CMD.hash_stop` bit and wait for the `hmac_done` interrupt (or poll the interrupt status register).
1. Save the context by reading the `DIGEST_0`..`15` and `MSG_LENGTH_`{`LOWER`,`UPPER`} registers.
If the operation is keyed HMAC, the values of `KEY_0`..`X` registers also need to be maintained as part of the context, where `X` is the last register used for the given key length (e.g. for HMAC-256, `X=7`).
However, key registers cannot be read from SW, therefore SW must maintain key values as part of its own context during initialization.
Similarly, the value of the `CFG` register must also be preserved, and SW should keep its value separately, instead of reading it from `CFG` register.
1. Disable `sha_en` by updating `CFG` register, in order to clear the digest from stream A.
This is necessary to also prevent leakage of intermediate context of one SW thread to another.
1. Repeat steps 1-5 for message stream B.
1. Before restoring context, make sure that `sha_en` in `CFG` remains disabled.
1. Restore the context of message stream A by writing the `CFG`, `DIGEST_0`..`15`, and `MSG_LENGTH_`{`LOWER`,`UPPER`} registers.
In the case of keyed HMAC, `KEY_0`..`X` registers also need to be restored.
1. Enable `sha_en` of `CFG`, which enables HMAC again and locks down writing to the `DIGEST_0`..`15` registers from SW.
1. Continue processing message stream A by setting the `CMD.hash_continue` bit.
1. Write an arbitrary number of message blocks to HMAC's `MSG_FIFO`.
1. Continue this with as many message blocks and parallel message streams as needed.
The final hash for any message stream can be obtained at any time (no need for complete blocks) by setting `CMD.hash_process` and waiting for the `hmac_done` interrupt / status bit (or polling on the `STATUS.hmac_idle` bit) to indicate the ongoing operation has completed, and finally reading the digest from the `DIGEST` registers.

## Errors

When HMAC errors are triggered, the IP reports the error via [`INTR_STATE.hmac_err`](registers.md#intr_state).
The details of the error type is stored in [`ERR_CODE`](registers.md#err_code).

Error                        | Value | Description
-----------------------------|-------|---------------
`SwPushMsgWhenShaDisabled`   | `0x1` | The error is reported when SW writes data into MSG_FIFO when SHA is disabled. It may be due to SW routine error, or FI attacks. This error code is not used in the current version of the IP. Instead `SwPushMsgWhenDisallowed` is reported.
`SwHashStartWhenShaDisabled` | `0x2` | When HMAC detects the CMD.start while SHA is disabled, it reports this error code.
`SwUpdateSecretKeyInProcess` | `0x3` | Secret Key CSRs should not be modified during the hashing. This error is reported when those CSRs are revised during hashing.
`SwHashStartWhenActive`      | `0x4` | The error is reported when CMD.start is received while HMAC is running.
`SwPushMsgWhenDisallowed`    | `0x5` | After CMD.process is received, the MSG_FIFO should not by updated by SW. This error is reported in that case.
`SwInvalidConfig`            | `0x6` | SW has configured HMAC incorrectly.
`SwPushMsgWhenDisallowed`    | `0x5` | The error is reported when MSG_FIFO is being updated by SW with more message words when it is disallowed: either when the SHA-2 engine is disabled or the engine has not been triggered to start yet or it has been already triggered to finalize computation.
`SwInvalidConfig`            | `0x6` | The error is reported when HMAC has been configured incorrectly by SW, i.e. invalid digest size for SHA-2/HMAC modes or invalid key length for HMAC mode.

## FIFO Depth and Empty status

If the SW is slow and the SHA2 engine pops the data fast enough, the Message FIFO's depth may remain **0**.
The Message FIFO's `fifo_empty` status bit, however, is lowered for a cycle.

However, if the SHA-2 engine is currently busy, the Message FIFO may actually run full (indicated by the `fifo_full` status bit).
Resolving this conditions may take several dozens of cycles.
After the SHA-2 engine starts popping the data again, the Message FIFO will eventually run empty again and the `fifo_empty` status interrupt will fire.
Note that the `fifo_empty` status interrupt will not fire if i) the Message FIFO is not writable by software, or ii) after software has written either the `Process` or `Stop` command.

The recommended approach for software to write messages is:

1. Check the FIFO depth [`STATUS.fifo_depth`](registers.md#status). This represents the number of entry slots currently occupied in the FIFO.
2. Calculate the remaining size as `<max number of fifo entries> - <STATUS.fifo_depth>)`.
3. Write data to fill the remaining size.
4. Repeat until all data is written.
   In case the FIFO runs full (check [`STATUS.fifo_full`](registers.md#status)), software can optionally wait for the `fifo_empty` status interrupt before continuing.

If the FIFO runs full, software should not continue to write data into [`MSG_FIFO`](registers.md#msg_fifo) and first wait the status flag [`STATUS.fifo_full`](registers.md#status) to lower.
Whilst the FIFO is full, the HMAC will block writes until the FIFO has space which will cause back-pressure on the interconnect.

## Device Interface Functions (DIFs)

- [Device Interface Functions](../../../../sw/device/lib/dif/dif_hmac.h)

## Register Table

* [Register Table](registers.md#registers)
