# Manifest Format

<p style="color: red; text-align: right;">
  Status: Draft
</p>

This document describes the manifest format for boot stage images stored in flash.

OpenTitan secure boot, at a minimum, consists of three boot stages: `ROM`,
`ROM_EXT`, and the first owner boot stage, e.g. `BL0`. `ROM` is stored in the
read-only ROM while remaining stages are stored in flash. `ROM` and
`ROM_EXT` require the manifest described in this document to be at the start of
`ROM_EXT` and first owner boot stage images so that they can verify the
integrity and authenticity of the next stage and configure peripherals as
needed before handing over execution. Use of this manifest for stages following
the first owner boot stage is optional.

The following table lists the fields of the manifest along with their sizes,
alignments, and offsets from the start of the manifest in bytes. The last
column provides the corresponding C data type of each field for illustration
purposes. All manifest fields are stored little-endian and the total size of
the manifest is 1024 bytes.

| Field                 | Size (bytes) | Alignment (bytes) | Offset (bytes) | C Data Type    |
| --------------------- | ------------ | ----------------- | -------------- | -------------- |
| `ecdsa_signature`     | 64           | 4                 | 0              | `uint32_t[16]` |
| `reserved_signature`  | 160          | 4                 | 64             | `uint32_t[40]` |
| `reserved_unsigned`   | 160          | 4                 | 224            | `uint32_t[40]` |
| `selector_bits`       | 4            | 4                 | 384            | `uint32_t`     |
| `device_id`           | 32           | 4                 | 388            | `uint32_t[8]`  |
| `manuf_state_creator` | 4            | 4                 | 420            | `uint32_t`     |
| `manuf_state_owner`   | 4            | 4                 | 424            | `uint32_t`     |
| `life_cycle_state`    | 4            | 4                 | 428            | `uint32_t`     |
| `ecdsa_public_key`    | 64           | 4                 | 432            | `uint32_t[16]` |
| `reserved_public_key` | 160          | 4                 | 496            | `uint32_t[40]` |
| `reserved`            | 152          | 4                 | 656            | `uint32_t[38]` |
| `on_demand_dice`      | 4            | 4                 | 808            | `uint32_t`     |
| `manifest_base_address` | 4          | 4                 | 812            | `uint32_t`     |
| `address_translation` | 4            | 4                 | 816            | `uint32_t`     |
| `identifier`          | 4            | 4                 | 820            | `uint32_t`     |
| `manifest_version`    | 4            | 4                 | 824            | `uint32_t`     |
| `signed_region_end`   | 4            | 4                 | 828            | `uint32_t`     |
| `length`              | 4            | 4                 | 832            | `uint32_t`     |
| `version_major`       | 4            | 4                 | 836            | `uint32_t`     |
| `version_minor`       | 4            | 4                 | 840            | `uint32_t`     |
| `security_version`    | 4            | 4                 | 844            | `uint32_t`     |
| `timestamp`           | 8            | 4                 | 848            | `uint32_t[2]`  |
| `binding_value`       | 32           | 4                 | 856            | `uint32_t[8]`  |
| `max_key_version`     | 4            | 4                 | 888            | `uint32_t`     |
| `code_start`          | 4            | 4                 | 892            | `uint32_t`     |
| `code_end`            | 4            | 4                 | 896            | `uint32_t`     |
| `entry_point`         | 4            | 4                 | 900            | `uint32_t`     |
| `extensions`          | 120          | 4                 | 904            | `uint32_t[30]` |


# Field Descriptions

*   `ecdsa_signature`: ECDSA P256 signature of the image generated using a NIST
    P256 ECC key and the SHA-256 hash function.

*   `reserved_signature`: Reserved bytes for signature.

*   `reserved_unsigned`: Reserved bytes. These bytes are not signed by the signature.
    The signed region of an image starts immediately after this field and ends
    at the end of the image.

*   `selector_bits`: This field, along with the following four fields, is used
    to constrain a boot stage image to a set of devices based on their device
    IDs, creator and/or manufacturing states and life cycle states. Bits of
    this field determine which fields (or individual words of a field as in
    the case of `device_id`) must be read from the hardware during
    verification. Unselected fields must be set to
    `MANIFEST_USAGE_CONSTRAINT_UNSELECTED_WORD_VAL` to be able to generate a
    consistent value during verification. Bits 0-7 are mapped to words 0-7 of
    `device_id` and bits 8-10 are mapped to `manuf_state_creator`,
    `manuf_state_owner`, and `life_cycle_state`, respectively.

*   `device_id`: Device identifier value which is compared against the
    `DEVICE_ID` value stored in the `HW_CFG0` partition in OTP. Mapped to bits
     0-7 of `selector_bits`.

*   `manuf_state_creator`: Device silicon creator manufacturing status compared
    against the `CREATOR_SW_MANUF_STATUS` value stored in the `CREATOR_SW_CFG`
    partition in OTP. Mapped to bit 8 of `selector_bits`.

*   `manuf_state_owner`: Device silicon owner manufacturing status compared
    against the `OWNER_SW_MANUF_STATUS` value stored in the `OWNER_SW_CFG`
    partition in OTP. Mapped to bit 9 of `selector_bits`.

*   `life_cycle_state`: Device life cycle state compared against the state
    reported by the life cycle controller. Mapped to bit 10 of `selector_bits`.

*   `ecdsa_public_key`: Signer's ECDSA NIST P256 ECC public key.

*   `reserved_public_key`: Reserved bytes for public key.

*   `reserved`: Reserved bytes. When allocating reserved bytes, please allocate from
    the end of this field to allow for the potential size expansion of the public key
    field above.

*   `on_demand_dice`: DICE certificate refresh mode. If this field is `kHardenedBoolTrue`,
    DICE operates in On-Demand mode. Otherwise (including default `kHardenedBoolFalse`
    or legacy `0xa5a5a5a5`), the stage operates in On-Change mode. The field is only
    effective in ROM_EXT's manifest.

*   `manifest_base_address`: Absolute MMIO address where the manifest is expected
    to be placed. When set to the legacy unset value (`0xa5a5a5a5`), it is treated
    as bank base + 64 KiB.

*   `address_translation`: A hardened boolean representing whether address
    translation should be used for the `ROM_EXT` (see the [Ibex wrapper
    documentation](https://opentitan.org/book/hw/ip/rv_core_ibex)).
    This value should be either `0x739` (true) or `0x1d4` (false).

*   `identifier`: Image identifier used to identify boot stage images. The
    value of this field must be `0x4552544f` (ASCII: "OTRE") for a `ROM_EXT`
    image and `0x3042544f` (ASCII: "OTB0") for the first owner stage.

*   `manifest_version`: Manifest format major and minor version. These version
    values can be used to maintain or break forward compatibility in ROM while
    preserving backward compatibility in ROM_EXT. ROM requires the major version
    to be `kManifestVersionMajor2`.

*   `signed_region_end`: Offset of the end of the signed region relative to the
    start of the manifest.

*   `length`: Length of the image (including the manifest) in bytes.

*   `version_major`: Major version of the image.

*   `version_minor`: Minor version of the image.

*   `security_version`: Security version of the image used for anti-rollback
    protection. Must be a monotonically increasing integer.

*   `timestamp`: Unix timestamp of the creation time of the image. 64 bits with
    32-bit alignment.

*   `binding_value`: Binding value used by the [key manager][key_manager] to
    derive secret values. A change in this value changes the secret value of
    the key manager, and consequently, the versioned keys and identity seeds
    generated at subsequent boot stages.

*   `max_key_version`: Maximum allowed version for keys generated by the
    [key manager][key_manager] at the next boot stage.

*   `code_start`: Offset of the start of the executable region of the image
    from the start of the manifest in bytes. Must be 4-byte word aligned.

*   `code_end`: Offset of the end of the executable region of the image
    (exclusive) from the start of the manifest in bytes. Note that the range
    from `code_start` to `code_end` must cover all machine instructions, i.e.
    .vectors, .crt, and .text, in the image. Must be 4-byte word aligned.

*   `entry_point`: Offset of the first instruction to execute in the image from
    the start of the manifest in bytes. Must be 4-byte word aligned.

*   `extensions`: Extensions.

[key_manager]: https://opentitan.org/book/hw/ip/keymgr
