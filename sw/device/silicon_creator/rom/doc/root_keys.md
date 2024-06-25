## Root Keys in OTP (Earl Grey)

GitHub Tracking Issue:
[#21204](https://github.com/lowRISC/opentitan/issues/21204)

Earl Grey's secure boot root keys are now provisioned in OTP memory at
manufacturing time, similar to the Darjeeling architecture. This allows the
Silicon Creator to assign keys based on SKU configuration, enabling key rotation
and also provisioning of keys for Silicon Owners that act as effective Silicon
Creators.

## Supported Keys

OpenTitan is required to support hybrid signature schemes for secure boot. For
Earl Grey, this is based on ECDSA-P256-SHA256 and SLH-DSA. In this document and
in the code base we use "SPHINCS+", "spx", and/or "spx+" to refer to SLH-DSA.

The following sections cover the data structures used to support these signature
verification schemes.

### Common Key Header

All keys in the current Earl Grey implementation use a common `key_type` and a
`key_id` field. The `key_id` represents the first `uint32_t` word of the public
key, independent of whether the key is ECDSA-P256 or SLH-DSA.

The `key_type` determines the life cycle states in which the key is enabled for
secure boot verification. The value can be one of the following:

*   `kSigverifyKeyTypeInvalid`: Applicable to empty key slots.
*   `kSigverifyKeyTypeTest`: Applicable to devices in TEST\_UNLOCKED and RMA
    states.
*   `kSigverifyKeyTypeProd`: Applicable to devices in PROD, PROD\_END or DEV
    states.
    *   In DEV state, debug unlock functionality is allowed after the ROM\_EXT
        hands over execution to the first Silicon Owner code partition.
*   `kSigverifyKeyTypeDev`: Applicable to devices in DEV state and signed with a
    key that allows debugging of the ROM and ROM\_EXT.

The following data structure represents the common key header:

### ECDSA-P256 Key

Each ECDSA-P256 Key requires 68 bytes of OTP storage.

The `key_type` determines the life cycle states in which the key is enabled for
secure boot verification.

### SLH-DSA Key

Each SLH-DSA key requires 40 bytes of OTP storage.

The `key_type` determines the life cycle states in which the key is enabled for
secure boot verification.

The config parameter is used to select the configuration parameters between
SPHINCS+-SHA2-128s and SPHINCS+-SHA2-128s-q20. More details on configuration
options can be found in https://eprint.iacr.org/2022/1725.pdf.

## OTP

### Code Sign Partitions

The `ROT_CREATOR_AUTH_CODESIGN` OTP partition is used to store four P-256 keys
and four SLH-DSA keys. The partition requires 464 bytes of software visible
storage. The partition is locked at manufacturing time to protect against
malicious write attempts. The likelihood of a successful write is low, but the
attacker may be able to weaken the key by finding a write value that results in
a valid integrity code update.

The `ROT_CREATOR_AUTH_STATE` OTP partition is used to capture the state of each
key slot. Each key can be in one of the following states: `BLANK`,
`PROVISIONED`, `REVOKED`. The encoded values are such that transitions between
`BLANK` → `PROVISIONED` → `REVOKED` are possible without causing ECC errors
(this is a mechanism similar to how we manage life cycle state transitions). The
partition is left unlocked to allow `STATE` updates in the field. The `ROM_EXT`
is required to lock access to the OTP Direct Access Interface to prevent DoS
attacks from malicious code executing on Silicon Owner partitions. DAI write
locking is available in Earl Grey (see
[#20348](https://github.com/lowRISC/opentitan/issues/20348)) for more details.

### Integrity Protection

Since the keys are stored in a software partition, there is no runtime mechanism
available in hardware to perform continuous integrity checks. Similarly, there
is no support for detecting any integrity issues propagated through the bus. The
ROM is required to implement integrity checks before using any key material.

The `ROT_CREATOR_AUTH_CODESIGN_BLOCK_SHA2_256_HASH`field inside the
`ROT_CREATOR_AUTH_CODESIGN` partition must be provisioned with the SHA2-256
digest calculated from all the key slots processed as one contiguous block. The
ROM must verify the hash after loading the keys into SRAM and before any key
operations. Once the keys are loaded into SRAM, the ROM relies on the SRAM and
the integrity protection mechanism to perform detection and escalation of any
potential attacks.

## Key Provisioning

The keys are provisioned at manufacturing time when the device is in one of the
`TEST_UNLOCKED` states. `KEY0` will be provisioned with a key for
`TEST_UNLOCKED` and `RMA` life cycle states. `KEY1` to `KEY3` are provisioned
with mission mode keys (i.e. `kSigverifyKeyTypeProd` or `kSigverifyKeyTypeDev`).
Mission mode keys are managed by the SKU owner, which may be an entity
representing the Silicon Creator or the Silicon Owner.

> **There must be at least one valid key provisioned in the device before enabling
> ROM execution.**
