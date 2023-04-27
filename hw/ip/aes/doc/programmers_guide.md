# Programmer's Guide

This section discusses how software can interface with the AES unit.


## Clear upon Reset

Upon reset, the AES unit will first reseed the internal PRNGs for register clearing and masking via EDN, and then clear all key, IV and data registers with pseudo-random data.
Only after this sequence has finished, the unit becomes idle (indicated in [`STATUS.IDLE`](registers.md#status)).
The AES unit is then ready for software initialization.
Note that at this point, the key, IV and data registers' values can no longer be expected to match the reset values.


## Initialization

Before initialization, software must ensure that the AES unit is idle by checking [`STATUS.IDLE`](registers.md#status).
If the AES unit is not idle, write operations to [`CTRL_SHADOWED`](registers.md#ctrl_shadowed), the Initial Key registers [`KEY_SHARE0_0`](registers.md#key_share0) - [`KEY_SHARE1_7`](registers.md#key_share1) and initialization vector (IV) registers [`IV_0`](registers.md#iv) - [`IV_3`](registers.md#iv) are ignored.

To initialize the AES unit, software must first provide the configuration to the [`CTRL_SHADOWED`](registers.md#ctrl_shadowed) register.
Since writing this register may initiate the reseeding of the internal PRNGs, software must check that the AES unit is idle before providing the initial key.
Then software must write the initial key to the Initial Key registers [`KEY_SHARE0_0`](registers.md#key_share0) - [`KEY_SHARE1_7`](registers.md#key_share1).
The key is provided in two shares:
The first share is written to [`KEY_SHARE0_0`](registers.md#key_share0) - [`KEY_SHARE0_7`](registers.md#key_share0) and the second share is written to [`KEY_SHARE1_0`](registers.md#key_share1) - [`KEY_SHARE1_7`](registers.md#key_share1).
The actual initial key used for encryption corresponds to the value obtained by XORing [`KEY_SHARE0_0`](registers.md#key_share0) - [`KEY_SHARE0_7`](registers.md#key_share0) with [`KEY_SHARE1_0`](registers.md#key_share1) - [`KEY_SHARE1_7`](registers.md#key_share1).
Note that all registers are little-endian.
The key length is configured using the KEY_LEN field of [`CTRL_SHADOWED`](registers.md#ctrl_shadowed).
Independent of the selected key length, software must always write all 8 32-bit registers of both shares.
Each register must be written at least once.
The order in which the key registers are written does not matter.
Anything can be written to the unused key registers of both shares, however, random data is preferred.
For AES-128 ,the actual initial key used for encryption is formed by XORing [`KEY_SHARE0_0`](registers.md#key_share0) - [`KEY_SHARE0_3`](registers.md#key_share0) with [`KEY_SHARE1_0`](registers.md#key_share1) - [`KEY_SHARE1_3`](registers.md#key_share1).
For AES-192, the actual initial key used for encryption is formed by XORing [`KEY_SHARE0_0`](registers.md#key_share0) - [`KEY_SHARE0_5`](registers.md#key_share0) with [`KEY_SHARE1_0`](registers.md#key_share1) - [`KEY_SHARE1_5`](registers.md#key_share1).

If running in CBC, CFB, OFB or CTR mode, software must also write the IV registers [`IV_0`](registers.md#iv) - [`IV_3`](registers.md#iv).
Since providing the initial key initiate the reseeding of the internal PRNGs, software must check that the AES unit is idle before writing the IV registers.
These registers are little-endian, but the increment of the IV in CTR mode is big-endian (see [Recommendation for Block Cipher Modes of Operation](https://nvlpubs.nist.gov/nistpubs/Legacy/SP/nistspecialpublication800-38a.pdf)).
Each IV register must be written at least once.
The order in which these registers are written does not matter.
Note that the AES unit automatically updates the IV registers when running in CBC, CFB, OFB or CTR mode (after having consumed the current IV value).
To start the encryption/decryption of a new message, software must wait for the AES unit to become idle and then provide new values to the IV registers.

## Block Operation

For block operation, software must initialize the AES unit as described in the previous section.
In particular, the AES unit must be configured to run in normal/automatic mode.
This is indicated by the MANUAL_OPERATION bit in [`CTRL_SHADOWED`](registers.md#ctrl_shadowed) reading as `0`.
It ensures that the AES unit:
1. Automatically starts encryption/decryption when new input data is available.
1. Does not overwrite previous output data that has not yet been read by the processor.

Then, software must:
1. Ensure that the INPUT_READY bit in [`STATUS`](registers.md#status) is `1`.
1. Write Input Data Block `0` to the Input Data registers [`DATA_IN_0`](registers.md#data_in) - [`DATA_IN_3`](registers.md#data_in).
   Each register must be written at least once.
   The order in which these registers are written does not matter.
1. Wait for the INPUT_READY bit in [`STATUS`](registers.md#status) to become `1`, i.e. wait for the AES unit to load Input Data Block `0` into the internal state register and start operation.
1. Write Input Data Block `1` to the Input Data registers.

Then for every Data Block `I=0,..,N-3`, software must:
1. Wait for the OUTPUT_VALID bit in [`STATUS`](registers.md#status) to become `1`, i.e., wait for the AES unit to finish encryption/decryption of Block `I`.
   The AES unit then directly starts processing the previously input block `I+1`
2. Read Output Data Block `I` from the Output Data registers [`DATA_OUT_0`](registers.md#data_out) - [`DATA_OUT_3`](registers.md#data_out).
   Each register must be read at least once.
   The order in which these registers are read does not matter.
3. Write Input Data Block `I+2` into the Input Data register.
   There is no need to explicitly check INPUT_READY as in the same cycle OUTPUT_VALID becomes `1`, the current input is loaded in (meaning INPUT_READY becomes `1` one cycle later).

Once all blocks have been input, the final data blocks `I=N-2,N-1` must be read out:
1. Wait for the OUTPUT_VALID bit in [`STATUS`](registers.md#status) to become `1`, i.e., wait for the AES unit to finish encryption/decryption of Block `I`.
2. Read Output Data Block `I` from the Output Data register.

Note that interrupts are not provided, the latency of the AES unit is such that they are of little utility.

The code snippet below shows how to perform block operation.

```c
  // Enable autostart, disable overwriting of previous output data. Note the control register is
  // shadowed and thus needs to be written twice.
  uint32_t aes_ctrl_val =
      (op & AES_CTRL_SHADOWED_OPERATION_MASK) << AES_CTRL_SHADOWED_OPERATION_OFFSET |
      (mode & AES_CTRL_SHADOWED_MODE_MASK) << AES_CTRL_SHADOWED_MODE_OFFSET |
      (key_len & AES_CTRL_SHADOWED_KEY_LEN_MASK) << AES_CTRL_SHADOWED_KEY_LEN_OFFSET |
      0x0 << AES_CTRL_SHADOWED_MANUAL_OPERATION_OFFSET;
  REG32(AES_CTRL_SHADOWED(0)) = aes_ctrl_val;
  REG32(AES_CTRL_SHADOWED(0)) = aes_ctrl_val;

  // Write key - Note: All registers are little-endian.
  for (int j = 0; j < 8; j++) {
    REG32(AES_KEY_SHARE0_0(0) + j * 4) = key_share0[j];
    REG32(AES_KEY_SHARE1_0(0) + j * 4) = key_share1[j];
  }

  // Write IV.
  for (int j = 0; j < 4; j++) {
    REG32(AES_IV_0(0) + j * 4) = iv[j];
  }

  // Write Input Data Block 0.
  for (int j = 0; j < 4; j++) {
    REG32(AES_DATA_IN_0(0) + j * 4) = input_data[j];
  }

  // Wait for INPUT_READY bit
  while (!((REG32(AES_STATUS(0)) >> AES_STATUS_INPUT_READY) & 0x1)) {
  }

  // Write Input Data Block 1
  for (int j = 0; j < 4; j++) {
    REG32(AES_DATA_IN_0(0) + j * 4) = input_data[j + 4];
  }

  // For Data Block I=0,...,N-1
  for (int i = 0; i < N; i++) {

    // Wait for OUTPUT_VALID bit
    while (!((REG32(AES_STATUS(0)) >> AES_STATUS_OUTPUT_VALID) & 0x1)) {
    }

    // Read Output Data Block I
    for (int j = 0; j < 4; j++) {
      output_data[j + i * 4] = REG32(AES_DATA_OUT_0(0) + j * 4);
    }

    // Write Input Data Block I+2 - For I=0,...,N-3 only.
    if (i < N - 2) {
      for (int j = 0; j < 4; j++) {
        REG32(AES_DATA_IN_0(0) + j * 4) = input_data[j + 4 * (i + 2)];
      }
    }
  }

```


## Padding

For the AES unit to automatically start encryption/decryption of the next data block, software is required to always update all four Input Data registers [`DATA_IN_0`](registers.md#data_in) - [`DATA_IN_3`](registers.md#data_in) and read all four Output Data registers [`DATA_OUT_0`](registers.md#data_out) - [`DATA_OUT_3`](registers.md#data_out).
This is also true if the AES unit is operated in OFB or CTR mode, i.e., if the plaintext/ciphertext not necessarily needs to be a multiple of the block size (for more details refer to Appendix A of [Recommendation for Block Cipher Modes of Operation](https://nvlpubs.nist.gov/nistpubs/Legacy/SP/nistspecialpublication800-38a.pdf)).

In the case that the plaintext/ciphertext is not a multiple of the block size and the AES unit is operated in OFB or CTR mode, software can employ any form of padding for the input data of the last message block as the padding bits do not have an effect on the actual message bits.
It is recommended that software discards the padding bits after reading the output data.


## De-Initialization

After finishing operation, software must:
1. Disable the AES unit to no longer automatically start encryption/decryption by setting the MANUAL_OPERATION bit in [`CTRL_SHADOWED`](registers.md#ctrl_shadowed) to `1`.
1. Clear all key registers, IV registers as well as the Input Data and the Output Data registers with pseudo-random data by setting the KEY_IV_DATA_IN_CLEAR and DATA_OUT_CLEAR bits in [`TRIGGER`](registers.md#trigger) to `1`.

The code snippet below shows how to perform this task.

```c
  // Disable autostart. Note the control register is shadowed and thus needs to be written twice.
  uint32_t aes_ctrl_val = 0x1 << AES_CTRL_SHADOWED_MANUAL_OPERATION;
  REG32(AES_CTRL_SHADOWED(0)) = aes_ctrl_val;
  REG32(AES_CTRL_SHADOWED(0)) = aes_ctrl_val;

  // Clear all key, IV, Input Data and Output Data registers.
  REG32(AES_TRIGGER(0)) =
      (0x1 << AES_TRIGGER_KEY_IV_DATA_IN_CLEAR) |
      (0x1 << AES_TRIGGER_DATA_OUT_CLEAR);
```

## Device Interface Functions (DIFs)

* [DIF Listings](../../../../sw/device/lib/dif/dif_aes.h)
