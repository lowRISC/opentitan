# Boot Log

The OpenTitan boot process consists of three stages: `ROM`, `ROM_EXT`, and the first owner boot stage (e.g. `BL0`).
Both the `ROM_EXT` and `BL0` stages have two slots, A and B, to ensure reliable updates.
This means that the actual `ROM_EXT` and `BL0` slots executed during boot are determined at runtime.

OpenTitan stores this information in the retention SRAM as a `boot_log_t` struct to make it accessible to later boot stages.
The struct is 128 bytes long and is defined in [`boot_log.h`](../lib/boot_log.h).

## Field Descriptors

| Offset | Size (bytes) | Field                       | Description |
|-------:|-------------:|-----------------------------|-------------|
|      0 |           32 | `digest`                    | SHA-256 digest of the rest of the boot log (bytes 32 to 127), of type `hmac_digest_t`. |
|     32 |            4 | `identifier`                | Boot log identifier. The value of this field must be `0x474f4c42` (ASCII: "BLOG"). |
|     36 |            8 | `chip_version`              | Truncated commit hash of the ROM build (`scm_revision` field of the ROM's `build_info_t`). |
|     44 |            4 | `rom_ext_slot`              | `ROM_EXT` slot (A or B) used during boot, as a `boot_slot_t`. |
|     48 |            4 | `rom_ext_major`             | `ROM_EXT` major version number. |
|     52 |            4 | `rom_ext_minor`             | `ROM_EXT` minor version number. |
|     56 |            4 | `rom_ext_size`              | Size reserved for the `ROM_EXT` in flash (`CHIP_ROM_EXT_SIZE_MAX`). |
|     60 |            8 | `rom_ext_nonce`             | Nonce used for challenge/response boot services commands. |
|     68 |            4 | `bl0_slot`                  | `BL0` slot (A or B) used during boot, as a `boot_slot_t`. |
|     72 |            4 | `ownership_state`           | Ownership state of the chip, as an `ownership_state_t`. |
|     76 |            4 | `ownership_transfers`       | Number of ownership transfers this chip has had. |
|     80 |            4 | `rom_ext_min_sec_ver`       | Minimum security version permitted for `ROM_EXT` payloads. |
|     84 |            4 | `bl0_min_sec_ver`           | Minimum security version permitted for `BL0` (application) payloads. |
|     88 |            4 | `primary_bl0_slot`          | Primary `BL0` slot, as a `boot_slot_t`. |
|     92 |            4 | `retention_ram_initialized` | Whether the ROM initialized the retention SRAM on this boot, as a `hardened_bool_t`. |
|     96 |           32 | `reserved`                  | Padding to 128 bytes. |

Slots are encoded as `boot_slot_t` values: `0x5f5f4141` (ASCII: "AA__") for slot A and `0x42425f5f` (ASCII: "__BB") for slot B.

## Producers

The `ROM` initializes the boot log on every boot: it sets `identifier`, `chip_version` and `retention_ram_initialized`, records the `ROM_EXT` slot it boots in `rom_ext_slot`, and updates `digest`.
The `ROM_EXT` fills in the remaining fields and updates `digest` again.
A boot log is valid if `digest` matches its contents and `identifier` is `0x474f4c42` (see `boot_log_check()`).
