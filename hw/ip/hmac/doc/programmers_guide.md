# Programmer's Guide

This chapter shows how to use the HMAC-SHA256 IP by showing some snippets such
as initialization, initiating SHA-256 or HMAC process and processing the
interrupts. This code is not compilable but serves to demonstrate the IO
required.
More detailed and complete code can be found in the software under `sw/`, [ROM code](https://github.com/lowRISC/opentitan/blob/master/sw/device/silicon_creator/lib/drivers/hmac.c) and [HMAC DIF](https://github.com/lowRISC/opentitan/blob/master/sw/device/lib/dif/dif_hmac.c).

## Initialization

This section of the code describes initializing the HMAC-SHA256, setting up the
interrupts, endianness, and HMAC, SHA-256 mode. [`CFG.endian_swap`](registers.md#cfg) reverses
the byte-order of input words when software writes into the message FIFO.
[`CFG.digest_swap`](registers.md#cfg) reverses the byte-order in the final HMAC or SHA hash.

```c
void hmac_init(unsigned int endianess, unsigned int digest_endian) {
  HMAC_CFG(0) = HMAC_CFG_SHA_EN
              | HMAC_CFG_HMAC_EN
              | (endianess << HMAC_CFG_ENDIAN_SWAP_LSB)
              | (digest_endian << HMAC_CFG_DIGEST_SWAP_LSB);

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

## Triggering HMAC/SHA-256 engine

The following code shows how to send a message to the HMAC, the procedure is
the same whether a full HMAC or just a SHA-256 calculation is required (choose
between them using [`CFG.hmac_en`](registers.md#cfg)). In both cases the SHA-256 engine must be
enabled using [`CFG.sha_en`](registers.md#cfg) (once all other configuration has been properly set).
If the message is bigger than 512-bit, the software must wait until the FIFO
isn't full before writing further bits.

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

The HMAC IP prevents [`CFG`](registers.md#cfg) and [`KEY`](registers.md#key) registers from updating while the engine is processing messages.
Such attempts are discarded.
The [`KEY`](registers.md#key) register ignores any attempt to access the secret key in the middle of the process.
If the software tries to update the KEY, the IP reports an error through the Error FIFO. The error code is `SwUpdateSecretKeyInProcess`, `0x0003`.

## Saving and restoring the context

Software can let the HMAC IP process multiple message streams in a time-interleaved fashion by saving and restoring the context (i.e., parts of the hardware-internal state).

Such context switches are possible only at the boundary of complete message blocks (512 bit for SHA-256).
When SW doesn't know each instant at which a full message block is available, it can buffer data in memory until a block is full and only write HMAC's FIFOs once the buffer in memory contains a full message block.

The context that needs to be saved and restored is in the following registers: [`CFG`](registers.md#cfg), [`DIGEST_*`](registers.md#digest), and [`MSG_LENGTH_*`](registers.md#msg_length_lower).

Each message stream needs to be started *once* by setting the `CMD.hash_start` bit and finalized *once* by setting the `CMD.hash_process` bit.
To switch from one message stream to another, set the `CMD.hash_stop` bit, wait for the `hmac_done` interrupt (or status bit), save one context and restore the other, and then set the `CMD.hash_continue` bit.

Here is an example usage pattern of this feature:
1. Start processing message stream A by configuring HMAC and then setting the `CMD.hash_start` bit.
2. Write an arbitrary number of message blocks to HMAC's `MSG_FIFO`.
3. Stop HMAC by setting the `CMD.hash_stop` bit and wait for the `hmac_done` interrupt (or poll the interrupt status register).
4. Save the context by reading the `DIGEST_0`..`7` and `MSG_LENGTH_`{`LOWER`,`UPPER`} registers. (The values in the `CFG` register must also be preserved, but that is purely SW-controlled so doesn't need to be read from HW.)
5. Repeat steps 1-4 for message stream B.
6. Restore the context of message stream A by writing the `CFG`, `DIGEST_0`..`7`, and `MSG_LENGTH_`{`LOWER`,`UPPER`} registers.
7. Continue processing message stream A by setting the `CMD.hash_continue` bit.
8. Write an arbitrary number of message blocks to HMAC's `MSG_FIFO`.
9. Continue this with as many message blocks and parallel message streams as needed. The final hash for any message stream can be obtained at any time (no need for complete blocks) by setting `CMD.hash_process` and waiting for the `hmac_done` interrupt / status bit, finally reading the digest from the `DIGEST` registers.

## Errors

When HMAC sees errors, the IP reports the error via [`INTR_STATE.hmac_err`](registers.md#intr_state).
The details of the error type is stored in [`ERR_CODE`](registers.md#err_code).

Error                        | Value | Description
-----------------------------|-------|---------------
`SwPushMsgWhenShaDisabled`   | `0x1` | The error is reported when SW writes data into MSG_FIFO when SHA is disabled. It may be due to SW routine error, or FI attacks.
`SwHashStartWhenShaDisabled` | `0x2` | When HMAC detects the CMD.start when SHA is disabled, it reports this error code.
`SwUpdateSecretKeyInProcess` | `0x3` | Secret Key CSRs should not be modified during the hashing. This error is reported when those CSRs are revised in active.
`SwHashStartWhenActive`      | `0x4` | The error is reported when CMD.start is received while HMAC is running.
`SwPushMsgWhenDisallowed`    | `0x5` | After CMD.process is received, the MSG_FIFO should not by updated by SW. This error is reported in that case.



### FIFO_EMPTY

If the FIFO_FULL interrupt occurs, it is recommended the software does not write
more data into [`MSG_FIFO`](registers.md#msg_fifo) until the interrupt is cleared and the status
[`STATUS.fifo_full`](registers.md#status) is lowered. Whilst the FIFO is full the HMAC will block
writes until the FIFO has space which will cause back-pressure on the
interconnect.

## Device Interface Functions (DIFs)

- [Device Interface Functions](../../../../sw/device/lib/dif/dif_hmac.h)

## Register Table

* [Register Table](registers.md#registers)
