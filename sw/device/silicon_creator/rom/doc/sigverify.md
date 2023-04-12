# Mask ROM Signature Verification Module

This document describes the signature verification module (sigverify) which is responsible for verifying the authenticity and integrity of boot stages stored in eFlash, e.g. ROM\_EXT or the first owner boot stage.


## TL;DR

OpenTitan uses the [RSASSA-PKCS1-v1\_5](https://tools.ietf.org/html/rfc8017#section-8.2) signature scheme with SHA2-256, 3072-bit keys, and e=65537 (F4).
Sigverify can currently store up to 8 keys and supports three key types (roles): Test, Dev, and Prod.
Each key has a corresponding byte in OTP and can be irreversibly invalidated during manufacturing in case the corresponding private key is compromised.

## Dependencies

*   Drivers:
    *   HMAC for hash computations.
    *   OTP for key validity check and usage constraints.
    *   Life cycle controller for key validity check and usage constraints.
    *   OTBN for modular exponentiation.

## Signature Verification

Signature verification consists of four main steps:

1. Get the RSA public key to verify the signature of an image.
2. Compute the digest of the image.
3. Perform modular exponentiation to compute the encoded message.
4. Check the encoded message.

### Public Keys

[Manifests](../../rom_ext/doc/manifest.md) of in-flash boot stage images, e.g. ROM\_EXT or the first owner boot stage, contain the public key (exponent and modulus) for verifying their signatures.
While this information is useful for checking the integrity of an image off-target, e.g. using a developer utility, it's trivial for an attacker to sign an image with an arbitrary key.
In order to establish the authenticity of a manifest, sigverify uses the authorized public keys stored in ROM for signature verification.

Sigverify can currently store up to 8 authorized keys of 3 different types (roles): Test (manufacturing), dev (development), and prod (production).
Each authorized key has a corresponding byte (`hardened_byte_bool_t`) in the `CREATOR_SW_CFG_KEY_IS_VALID` OTP item that can be used to irreversibly invalidate that key during manufacturing in case the corresponding private key is compromised.
Validity of these keys are further gated by the life cycle state of the device: Test keys can only be used in TEST\_UNLOCKED and RMA life cycle states, dev keys can only be used in the DEV life cycle state, and prod keys can be used in all life cycle states.
The public key of a manifest must be both authorized and valid, i.e. not invalidated in OTP and allowed in the current life cycle state of the device, for sigverify to attempt to verify the signature of an image.
The following table summarizes the conditions under which each type of key is valid.
Note that key validity during manufacturing (TEST\_UNLOCKED) does not depend on the OTP value since it may not have been programmed yet.

|           | TEST_UNLOCKED   | PROD, PROD_END   | DEV   | RMA   |
|-----------|-----------------|------------------|-------|-------|
| Test keys | Yes             | No               | No    | OTP   |
| Dev keys  | No              | No               | OTP   | No    |
| Prod keys | Yes             | OTP              | OTP   | OTP   |

### Digest Computation

Sigverify uses SHA-256 for digest computation.
The signed region of an in-flash boot stage image starts immediately after the signature field of its manifest, i.e. its first field, and extends to the end of the image.
While signing an image, the digest of its signed area is computed as usual.
During verification in ROM, sigverify reads usage constraints from the device (instead of using the values in the manifest directly) and uses these values for computing the digest for signature verification:

```
digest = SHA256(usage_constraints_from_hw || rest_of_the_image).
```

The advantage of this approach is that it does not require any changes in signature generation or off-target signature verification.
See the usage constraints fields (`selector_bits`, `device_id`, `manuf_state_creator`, `manuf_state_owner`, `life_cycle_state`) in [manifest documentation](../../rom_ext/doc/manifest.md) for more details.
See this [document](https://docs.google.com/document/d/1V9O-YTaUVWoXMq85qIYaSS6x7Bl9Li4Z2KqZ6u_jG98/edit?resourcekey=0-TfuDj6NU3Ir0L1PrkcNyog) for a brief explanation of why this approach is not susceptible to length extension attacks.

### Modular Exponentiation

Sigverify has two redundant modular exponentiation implementations: one written entirely in software, and the other using OTBN.
While the hardware accelerated implementation is preferred, it's crucial to have both while we build confidence in the implementation.
Sigverify can use either one of them based on the value of the `CREATOR_SW_CFG_USE_SW_RSA_VERIFY` OTP item (defaults to SW implementation in TEST\_UNLOCKED).
When the OTBN implementation is chosen, the OTBN program (a binary blob in ROM generated from [verified assembly](https://github.com/lowRISC/opentitan/pull/10143)) and the input arguments are first copied to the instruction and data memory of OTBN, respectively.
Then, sigverify waits until OTBN finishes and copies the result back to main memory and proceeds with checking the encoded message.

Both implementations use Montgomery multiplication:

*   Compute _R<sup>2</sup>_.
*   Convert signature to Montgomery form _sig R mod n_ (1 Montgomery multiplication with R2).
*   Perform 16 Montgomery multiplications (e = 65537).
*   Convert back to get the encoded message, i.e. _sig<sup>e</sup> mod n_ (1 Montgomery multiplication with signature).

### Encoded Message Check

OpenTitan uses the [RSASSA-PKCS1-v1\_5](https://tools.ietf.org/html/rfc8017#section-8.2) signature scheme with SHA2-256, 3072-bit keys, e=65537 (F4) and does not support any other hash algorithms, key lengths, or exponents.
Thus, sigverify uses a hard-coded padding for checking the padding of the encoded message.
The rest of the encoded message, i.e.
the expected digest, is compared with the digest of the image being verified.
Sigverify uses a hardened [implementation]() to protect against fault injection attacks.

## Public APIs

```c
/**
 * Returns the key with the given ID.
 *
 * This function returns the key only if it can be used in the given life cycle
 * state and is valid in OTP. OTP check is performed only if the device is in a
 * non-test operational state (PROD, PROD_END, DEV, RMA).
 */
rom_error_t sigverify_rsa_key_get(uint32_t key_id, lifecycle_state_t lc_state,
                                  const sigverify_rsa_key_t **key);


/**
 * Verifies an RSASSA-PKCS1-v1_5 signature.
 *
 * The actual implementation that is used (software or OTBN) is determined by
 * the life cycle state of the device and the OTP value.
 */
rom_error_t sigverify_rsa_verify(const sigverify_rsa_buffer_t *signature,
                                 const sigverify_rsa_key_t *key,
                                 const hmac_digest_t *act_digest,
                                 lifecycle_state_t lc_state,
                                 uint32_t *flash_exec);

/**
 * Gets the usage constraints struct that is used for verifying a ROM_EXT.
 *
 * This function reads
 * - The device identifier from the life cycle controller,
 * - Creator and owner manufacturing states from the OTP,
 * - The life cycle state from life cycle controller, and
 * masks the fields of `usage_constraints` according to the given
 * `selector_bits`.
 */
void sigverify_usage_constraints_get(
    uint32_t selector_bits, manifest_usage_constraints_t *usage_constraints);

```

## Testing

Unit tests will be used to verify the algorithmic components of the software implementation, i.e. modular exponentiation and encoded message check, key retrieval, and behavior under different OTP values and life cycle states.
Functional tests will be used to verify both the software and the OTBN implementations on target hardware.
Sigverify will also have adversarial and random tests.
