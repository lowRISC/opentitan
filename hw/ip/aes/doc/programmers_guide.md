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

## Galois/Counter Mode (GCM)

GCM is a mode of Authenticated Encryption with Additional Data (AEAD) specified in [NIST 800-38D](https://nvlpubs.nist.gov/nistpubs/Legacy/SP/nistspecialpublication800-38d.pdf) and widely adopted in industry.
At a high level, GCM builds on top of the ECB and CTR block cipher modes of operation as well as a Galois Field GF(2^128) multiplication for the integrity tag computation (GHASH).
The AES unit follows a hybrid implementation approach where software cycles the AES hardware unit through the different phases of GCM.
To support context switching similar to the other AES block cipher modes of operation which only require reading the IV registers [`IV_0`](registers.md#iv) - [`IV_3`](registers.md#iv), software can switch the AES unit into special phases for saving and restoring also GHASH contexts.
How to cycle the hardware through the different GCM phases and how to save and restore full GCM contexts is explained in detail below.

Additional notes:
- This implementation uses a fixed IV length of 96 bits, thereby following the recommendation of [NIST 800-38D (Section 5.2.1.1)](https://nvlpubs.nist.gov/nistpubs/Legacy/SP/nistspecialpublication800-38d.pdf).
- This implementation uses a fixed tag length of 128 bits.
  Software is free to discard unused bits.

### GCM Encryption

To perform an GCM encryption, software performs the following steps:

1. Software configures the AES unit in GCM mode by setting the [`CTRL_SHADOWED.MODE`](registers.md#ctrl_shadowed) field to `AES_GCM` and the `OPERATION` field to `AES_ENC`.
   Writing this register clears internal counters and tracking logic and starts a new message.
   Software then sets [`CTRL_GCM_SHADOWED.PHASE`](registers.md#ctrl_gcm_shadowed) to `GCM_INIT` and the `NUM_VALID_BYTES` field to `16`.
   Internally, this configures the AES block in ECB mode.
   After configuring the encryption key, software writes the 96-bit IV to the IV registers [`IV_0`](registers.md#iv) - [`IV_2`](registers.md#iv) and `0` to IV register [`IV_3`](registers.md#iv).
   The hardware will then perform two operations:
   1. It encrypts the all-zero vector and stores the result in the hash subkey `H` registers internal to the GHASH module and increments the counter value (content of the IV Registers) using the inc32 function.
   1. It encrypts the incremented IV to form the encrypted initial counter block `S` and loads that the GHASH module.
      The counter value is again incremented using the inc32 function.

   Note that when running in manual mode, software must explicitly trigger both these operations by setting the START bit in [`TRIGGER`](registers.md#trigger) to `1`, waiting for the AES unit to become idle, and then again setting the START bit.

1. Software configures [`CTRL_GCM_SHADOWED.PHASE`](registers.md#ctrl_gcm_shadowed) to `GCM_AAD` and the `NUM_VALID_BYTES` field to `16`.
   This configures the module internally to forward any input provided via the Input Data registers [`DATA_IN_0`](registers.md#data_in) - [`DATA_IN_3`](registers.md#data_in) to the GHASH unit but NOT to the AES cipher core. Software then inputs the additional authenticated data (AAD) to the Input Data registers block by block.
   To see if the AES unit is ready to accept the next block, software can query the [`STATUS.INPUT_READY`](registers.md#status) bit.

   For the last block and only in case the block is not full, software first waits for the AES unit to become idle by querying the [`STATUS.IDLE`](registers.md#status) bit, and then sets the [`CTRL_GCM_SHADOWED.NUM_VALID_BYTES`](registers.md#ctrl_gcm_shadowed) field to the number of valid bytes.
   For all other blocks, this field must hold the value `16`.
   Internally, invalid bytes are tied to zero at the input of the GHASH module.

1. Software configures [`CTRL_GCM_SHADOWED.PHASE`](registers.md#ctrl_gcm_shadowed) to `GCM_TEXT` and the `NUM_VALID_BYTES` field to `16`.
   This configures the module internally to run in CTR mode: Any input provided via the Input Data registers [`DATA_IN_0`](registers.md#data_in) - [`DATA_IN_3`](registers.md#data_in) is XORed to the output of the AES cipher core and then fed to the input of the GHASH module as well as to the Output Data registers [`DATA_OUT_0`](registers.md#data_out) - [`DATA_OUT_3`](registers.md#data_out).
   Software provides the plaintext to the Input Data registers block by block.
   Note that for maximum performance, the AES unit supports having 3 data blocks in flight:
   1. One in the Input Data registers waiting to get loaded into the cipher core,
   2. one being processed by the core, and
   3. one in the Output Data registers waiting to get read by software.

   For details, refer to the [Block Operation section above](#block-operation).
   To see if the module is ready to accept the next block, software can query the [`STATUS.INPUT_READY`](registers.md#status) bit.
   Software reads the ciphertext from the Output Data registers.
   To see if the module has valid output data, software can query the [`STATUS.OUTPUT_VALID`](registers.md#status) bit.

   For the last block and only in case the block is not full, software first waits for the AES unit to become idle by querying the [`STATUS.IDLE`](registers.md#status) bit, and then sets the [`CTRL_GCM_SHADOWED.NUM_VALID_BYTES`](registers.md#ctrl_gcm_shadowed) field to the number of valid bytes.
   For all other blocks, this field must hold the value `16`.
   Internally, invalid bytes are tied to zero at the input of the GHASH module.

1. Software configures [`CTRL_GCM_SHADOWED.PHASE`](registers.md#ctrl_gcm_shadowed) to `GCM_TAG` and the `NUM_VALID_BYTES` field to `16`.
   This configures the module internally to forward any input provided via the Input Data registers [`DATA_IN_0`](registers.md#data_in) - [`DATA_IN_3`](registers.md#data_in) to the GHASH module but NOT to the AES cipher core.
   Software then provides a single data block of 128 bits containing the length of the AAD as well as the length of the ciphertext.
   This causes the GHASH module to produce the final authentication tag which is then written to the Output Data registers [`DATA_OUT_0`](registers.md#data_out) - [`DATA_OUT_3`](registers.md#data_out).

### GCM Decryption

To perform an GCM decryption, software performs the following steps:

1. Software configures the AES unit in GCM mode by setting the [`CTRL_SHADOWED.MODE`](registers.md#ctrl_shadowed) field to `AES_GCM` and the `OPERATION` field to `AES_DEC`.
   The rest of this step is identical to the encryption case.

1. This step is identical to the encryption case.

1. This step is identical to the encryption case.
   The only difference is that internally to the AES unit, the content of the Input Data registers, i.e., the ciphertext, is fed to the AES cipher core as well as to the GHASH module via the register holding the previous input data.

1. This step is identical to the encryption case.
   Software reads the final authentication tag from the Output Data registers [`DATA_OUT_0`](registers.md#data_out) - [`DATA_OUT_3`](registers.md#data_out) and compares the obtained value against the expected tag.

### GCM Context Saving

Interrupting an ongoing encryption/decryption operation is only possible in Step 2 or 3 (AAD or plaintext/ciphertext processing) and only after having processed a first AAD or plaintext/ciphertext block.

1. Software needs to wait for the AES unit to become idle (see [`STATUS.IDLE`](registers.md#status)).

1. Software configures the [`CTRL_GCM_SHADOWED.PHASE`](registers.md#ctrl_gcm_shadowed) to `GCM_SAVE` and the `NUM_VALID_BYTES` field to `16`.
   Software should check the [`CTRL_GCM_SHADOWED.PHASE`](registers.md#ctrl_gcm_shadowed) field.
   If it does not read as `GCM_TAG`, the previous write operation did not go through, e.g., because moving to this phase is only possible after having processed a first AAD or plaintext/ciphertext block.
   If it reads as `GCM_TAG`, this means the AES unit outputs the current state of the GHASH module via Output Data registers [`DATA_OUT_0`](registers.md#data_out) - [`DATA_OUT_3`](registers.md#data_out) where software can read it.

1. Software reads the current content of the IV registers [`IV_0`](registers.md#iv) - [`IV_3`](registers.md#iv).

### GCM Context Restoring

To restore a context, software must perform the following steps:

1. Software configures the AES unit in GCM mode by setting the [`CTRL_SHADOWED.MODE`](registers.md#ctrl_shadowed) field to `AES_GCM` and the `OPERATION` field to `AES_ENC`/`AES_DEC`.
   Writing this register clears internal counters and tracking logic and starts a new message.
   Software then sets [`CTRL_GCM_SHADOWED.PHASE`](registers.md#ctrl_gcm_shadowed) to `GCM_INIT` and the `NUM_VALID_BYTES` field to `16`.
   Internally, this configures the AES block in ECB mode.
   After configuring the encryption key, software writes the 96-bit IV to the IV registers [`IV_0`](registers.md#iv) - [`IV_2`](registers.md#iv) and `0` to IV register [`IV_3`](registers.md#iv).
   The hardware will then perform two operations:
   1. It encrypts the all-zero vector and stores the result in the hash subkey `H` registers internal to the GHASH module and increment the counter value (content of the IV Registers) using the inc32 function.
   1. It encrypts the incremented IV to form the encrypted initial counter block `S` and loads that the GHASH module.
      The counter value is again incremented using the inc32 function.

   Note that when running in manual mode, software must explicitly trigger both these operations by setting the START bit in [`TRIGGER`](registers.md#trigger) to `1`, waiting for the AES unit to become idle, and then again setting the START bit.

   Software then waits for the AES unit to become idle again (see [`STATUS.IDLE`](registers.md#status)).
   The hardware is now ready to restore a previously saved GCM context.

1. Software configures [`CTRL_GCM_SHADOWED.PHASE`](registers.md#ctrl_gcm_shadowed) to `GCM_RESTORE` and the `NUM_VALID_BYTES` field to `16`.
   Internally, this configures the AES unit to restore the internal state of the GHASH module based on the content of the Input Data registers [`DATA_IN_0`](registers.md#data_in) - [`DATA_IN_3`](registers.md#data_in).
   Software provides the previously saved GHASH context to the Input Data registers.
   Then, it waits for the AES unit to become idle again (see [`STATUS.IDLE`](registers.md#status)).
   Software writes the previously saved IV into the IV registers [`IV_0`](registers.md#iv) - [`IV_3`](registers.md#iv).
   Note that even though just the content of [`IV_3`](registers.md#iv) is really different from the value after the initialization, software must write all four IV registers.

1. Software configures [`CTRL_GCM_SHADOWED.PHASE`](registers.md#ctrl_gcm_shadowed) to `GCM_AAD` or `GCM_TEXT` and the `NUM_VALID_BYTES` field to `16` to continue processing where it left off previously.

Note that since both the masked hash subkey `H` and the masked encrypted initial counter block `S` are recomputed by the AES cipher core as part of the context restoring, the context switching feature can be leveraged to effectively refresh their sharing thereby injecting fresh entropy into the GHASH module.

## Padding

For the AES unit to automatically start encryption/decryption of the next data block, software is required to always update all four Input Data registers [`DATA_IN_0`](registers.md#data_in) - [`DATA_IN_3`](registers.md#data_in) and read all four Output Data registers [`DATA_OUT_0`](registers.md#data_out) - [`DATA_OUT_3`](registers.md#data_out).
This is also true if the AES unit is operated in OFB or CTR mode, i.e., if the plaintext/ciphertext not necessarily needs to be a multiple of the block size (for more details refer to Appendix A of [Recommendation for Block Cipher Modes of Operation](https://nvlpubs.nist.gov/nistpubs/Legacy/SP/nistspecialpublication800-38a.pdf)).
The same also holds for the last AAD or plaintext/ciphertext block in GCM.

In the case that the AAD or plaintext/ciphertext is not a multiple of the block size and the AES unit is operated in OFB or CTR mode or in GCM, software can employ any form of padding for the input data of the last block as the padding bits do not have an effect on the actual message bits or the final authentication tag in case of GCM.
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
