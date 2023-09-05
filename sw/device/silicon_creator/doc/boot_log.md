# Boot Log

The OpenTitan boot process consists of three stages: `ROM`, `ROM_EXT`, and the first owner boot stage (e.g. `BL0`).
Both the `ROM_EXT` and `BL0` stages have two slots, A and B, to ensure reliable updates.
This means that the actual `ROM_EXT` and `BL0` slots executed during boot are determined at runtime.

OpenTitan stores this information in the retention SRAM as a `boot_log_t` struct to make it accessible to later boot stages.

## Field Descriptors

- `digest`: HMAC digest of type `hmac_digest_t` for data integrity.
- `identifier`: Boot log identifier. The value of this field must be `0x474c4f42` (ASCII: "BOLG").
- `chip_version`: `scm_revision` field from `chip_info`.
- `rom_ext_slot`: `ROM_EXT` slot (A or B) used during boot.
- `bl0_slot`: `BL0` slot (A or B) used during boot.
