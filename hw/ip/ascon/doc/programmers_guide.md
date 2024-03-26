# Programmer’s Guide

## Initializing the IP

As long as there is a key set, the IP can be used. However it is good practice not to rely on any default values but to configure the IP. The following settings should be configured in the following order:
1. Check if the IP is idle by reading STATUS.IDLE
2. Check for any errors by reading the STATUS.ascon_error. If there are any errors, perform a secure wipe by setting TRIGGER.wipe to 1.
3. Set CTRL_AUX_SHADOWED.force_data_overwrite and CTRL_AUX_SHADOWED.manual_start_trigger if appropriate.
4. Set CTRL_SHADOWED .sideload_key to use the key from the keymanager and set CTRL_SHADOWED.Operation (at the moment only authenticated encryption and decryption are supported). Writing to the CTRL_SHADOWED register will start a new transaction


## Interrupt Configuration

none


## Issuing Transactions
### Authenticated Encryption

1. Check if the IP is idle by ready STATUS.IDLE.
2. Configure the IP using the CTRL_SHADOWED register.
3. Write the key to KEY_SHARE0 and KEY_SHARE1. This is optional, if there is a previous key already present. Writes to the key registers are ignored in the case CTRL.sideload_key is set.
4. Write the nonce to NONCE_SHARE0 and NONCE_SHARE1. It is crucial to use a new, unique once for each encryption. The uniqueness is not checked by the IP,however the IP will indicate a missing nonce via the Error.no_nonce flag.
5. If there is any associated data, set the BLOCK_CTRL_SHADOWED.Data_type_start = AD_IN.
    1. If this is the last block of the associated data, set the BLOCK_CTRL_SHADOWED.Data_type_last = AD_IN and the BLOCK_CTRL_SHADOWED.VALID_BYTES to the amount of valid bytes.
    2. Check if the IP is ready to receive new data by reading STATUS.stall[^7]
    3. Write the associated data to the DATA_IN_SHARE_0 and DATA_IN_SHARE_1 register, depending on CTRL_SHADOWED.masked_ad_input. It is expected to only write multiples of one byte.
    4. In manual mode: Set TRIGGER.START
6. If there is any plaintext, set the BLOCK_CTRL_SHADOWED.Data_type_start = PT_IN.
    1. If this is the last block of plaintext, set the BLOCK_CTRL_SHADOWED.Data_type_last = PT_IN and the BLOCK_CTRL_SHADOWED.VALID_BYTES to the amount of valid bytes.
    2. Check if the IP is ready to receive new data by reading STATUS.stall. This step is optional, if this is not the first plaintext block and if the previous read of the ciphertext block was successful. In this case the IP is always ready to accept new data.
    3. Write the plaintext to the DATA_IN_SHARE_0 and DATA_IN_SHARE_1 register, depending on CTRL_SHADOWED.masked_msg_input. It is expected to only write multiples of one byte.
    4. In manual mode: Set TRIGGER.START
    5. Check OUTPUT_VALID.data_type to match CT_OUT and read the same amount of ciphertext from the MSG_OUT register.
7. Check OUTPUT_VALID.data_type to match TAG_OUT and read the tag from the TAG_OUT register.
8. Perform a secure wipe by writing to TRIGGER.WIPE to delete any key material, or if you want to use the same key for the next encryption, issue a new encryption by writing to CTRL_SHADOWED.


### Authenticated Decryption

1. Check if the IP is idle by ready STATUS.IDLE.
2. Configure the IP using the CTRL_SHADOWED register.
3. Write the key to KEY_SHARE0 and KEY_SHARE1. This is optional, if there is a previous key already present. Writes to the key registers are ignored in the case CTRL.sideload_key is set.
4. Write the corresponding NONCE to  NONCE_SHARE0 and NONCE_SHARE1. The IP will indicate a missing nonce via the Error.no_nonce flag.
5. If there is any associated data, set the BLOCK_CTRL_SHADOWED.Data_type_start = AD_IN.
    1. If this is the last block of associated data, set the BLOCK_CTRL_SHADOWED.Data_type_last = AD_IN and the BLOCK_CTRL_SHADOWED.VALID_BYTES to the amount of valid bytes.
    2. Check if the IP is ready to receive new data by reading STATUS.stall[^8]
    3. Write the associated data to the DATA_IN_SHARE_0 and DATA_IN_SHARE_1 register, depending on CTRL_SHADOWED.masked_ad_input. It is expected to only write multiples of one byte.
    4. In manual mode: Set TRIGGER.START
6. If there is any ciphertext, set the BLOCK_CTRL_SHADOWED.Data_type_start = CT_IN.
    1. If this is the last block of ciphertext, set the BLOCK_CTRL_SHADOWED.Data_type_last = CT_IN and the BLOCK_CTRL_SHADOWED.VALID_BYTES to the amount of valid bytes.
    2. Check if the IP is ready to receive new data by reading STATUS.stall. This step is optional, if this is not the first ciphertext block and if the previous read of the plaintext block was successful. In this case the IP is always ready to accept new data.
    3. Write the ciphertext to the DATA_IN_0 and DATA_IN_SHARE_1 register, depending on CTRL_SHADOWED.masked_msg_input. It is expected to only write multiples of one byte.
    4. In manual mode: Set TRIGGER.START
    5. Check OUTPUT_VALID.data_type to match PT_OUT and read the same amount of plaintext from the MSG_OUT register.
7. Write the tag to the TAG_IN register.
8. Check OUTPUT_VALID.tag_valid.
9. Perform a secure wipe by writing to TRIGGER.WIPE to delete any key material, or if you want to use the same key for the next encryption, issue a new encryption by writing to CTRL_SHADOWED.


### Hashing, eXtendable-output Function (XOF),  pseudorandom function (PRF)

Currently not supported.


## Exception Handling

A fatal alert cannot be recovered. A reset is needed
A recoverable alert can be recovered by rewriting the shadow registers.
If the Ascon unit is not able to accept new data, STATUS.STALL is set.
If there is an error due to a misconfiguration, this is indicated by the STATUS.ason_error flag and the ERROR register.

[^7]: This might be optional, to speed things up, if the programmer is sure the hardware is fast enough. At least for the unhardened version this should always be the case, as we are talking about less than 10 clock cycles
