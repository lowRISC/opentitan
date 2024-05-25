# Mask ROM Signature Verification Module

This document describes the signature verification module (sigverify) which is
responsible for verifying the authenticity and integrity of boot stages stored
in eFlash, e.g. `ROM_EXT` or the first owner boot stage.

## TL;DR

OpenTitan is required to support hybrid signature schemes for secure boot. For
Earl Grey, this is based on ECDSA-P256-SHA256 and SLH-DSA.

## Signature Verification

Signature verification consists of four main steps:

1.  Get the public key to verify the signature of an image.
2.  Compute the digest of the image.
3.  Perform signature verification to generate the encoded message.
4.  Check the encoded message.

### Public Keys

[Manifests](../../rom_ext/doc/manifest.md) of in-flash boot stage images, e.g.
`ROM_EXT` or the first owner boot stage, contain the public key for verifying
their signatures. While this information is useful for checking the integrity of
an image off-target, e.g. using a developer utility, it's trivial for an
attacker to sign an image with an arbitrary key. In order to establish the
authenticity of a manifest, sigverify uses the authorized public keys stored in
OTP for signature verification. See [Root Keys](./root_keys.md) documentation
for more details how the keys are configured and provisioned.

Validity of the public keys are gated by the life cycle state of the device:
Test keys can only be used in `TEST_UNLOCKED` and `RMA` life cycle states, dev
keys can only be used in the `DEV` life cycle state, and prod keys can be used
in all life cycle states. The public key of a manifest must be both authorized
and valid, i.e. not invalidated in OTP and allowed in the current life cycle
state of the device, for sigverify to attempt to verify the signature of an
image. The following table summarizes the conditions under which each type of
key is valid. Note that key validity during manufacturing (`TEST_UNLOCKED`) does
not depend on the OTP value since it may not have been programmed yet.

          | TEST_UNLOCKED | PROD, PROD_END | DEV | RMA
--------- | ------------- | -------------- | --- | ---
Test keys | Yes           | No             | No  | OTP
Dev keys  | No            | No             | OTP | No
Prod keys | Yes           | OTP            | OTP | OTP

### Digest Computation

Sigverify uses SHA-256 for digest computation. The signed region of an in-flash
boot stage image starts immediately after the signature field of its manifest,
i.e. its first field, and extends to the end of the image. While signing an
image, the digest of its signed area is computed as usual. During verification
in ROM, sigverify reads usage constraints from the device (instead of using the
values in the manifest directly) and uses these values for computing the digest
for signature verification:

```
digest = SHA256(usage_constraints_from_hw || rest_of_the_image).
```

The advantage of this approach is that it does not require any changes in
signature generation or off-target signature verification. See the usage
constraints fields (`selector_bits`, `device_id`, `manuf_state_creator`,
`manuf_state_owner`, `life_cycle_state`) in
[manifest documentation](../../rom_ext/doc/manifest.md) for more details. See
this
[document](https://docs.google.com/document/d/1V9O-YTaUVWoXMq85qIYaSS6x7Bl9Li4Z2KqZ6u_jG98/edit?resourcekey=0-TfuDj6NU3Ir0L1PrkcNyog)
for a brief explanation of why this approach is not susceptible to length
extension attacks.
