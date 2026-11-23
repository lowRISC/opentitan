# FIPS 140-3 Known Answer Tests (KATs) in ROM

This directory contains the end-to-end (E2E) test (`fips_kat_rom_test.c`) for validating the FIPS 140-3 Known Answer Test (KAT) vector table embedded in the Mask ROM `.fips_kat` section (`sw/device/silicon_creator/rom/fips_kat_table.h` and `sw/device/silicon_creator/rom/fips_kat_ptrs.c`).

## Transient 8 KiB NAPOT ePMP Mapping Model

`sw/device/silicon_creator/rom/rom.ld` pins `.fips_kat` to a fixed 8 KiB NAPOT-aligned window at the top of ROM:

- Base: `ORIGIN(rom) + LENGTH(rom) - 0x2000` (`kFipsKatRomEndOffset = 0x2000`)
- ePMP window size: `0x2000` (8 KiB, `kFipsKatRegionSize = 0x2000`)
- Reserved tail: `128 B` (`kFipsKatChipInfoReservedBytes = 128`) for non-confidential `.chip_info` (`[0x6FF80, 0x6FFE0)`) and the ECC-poisoned `rom_ctrl` digest words (`[0x6FFE0, 0x70000)`)
- Max usable KAT table size: `0x1F80` (8,064 B, `kFipsKatMaxTableSize = kFipsKatRegionSize - kFipsKatChipInfoReservedBytes`)

On Earl Grey Gen2 (192 KiB ROM at `[0x40000, 0x70000)`), this anchors the descriptor table at `[0x6E000, 0x70000)`, leaving **184 KiB** (`[0x40000, 0x6E000)`) below for Mask ROM code and `.rodata` with zero unused gap.
Linker assertion `ASSERT(_fips_kat_end <= _rom_chip_info_start)` and runtime validation against `kFipsKatMaxTableSize` ensure valid KAT offsets never reach `.chip_info` or `[0x6FFE0, 0x70000)`.

At `ROM_EXT` -> BL0 handoff, Mask ROM is unmapped by default under `mseccfg.MMWP`.
While `mseccfg.RLB` is set, `fips_kat_rom_test.c` exercises the transient read-only mapping lifecycle:

1. **Pre-map negative probes:** confirms loads from `kat_base`, `rom_base`, and the ECC-poisoned `rom_ctrl` digest (`rom_base + rom_size - 0x20`) raise `LoadAccessFault`.
2. **Transient NAPOT RO map:** programs free ePMP slot 0 (`pmpaddr0` / `pmpcfg0`) with `L=1, R=1, W=0, X=0, A=NAPOT` covering `[kat_base, kat_base + 8 KiB)`.
3. **During-map negative probes:** confirms stores to `kat_base`, execution at `kat_base`, and loads outside the window (`kat_base - 4`, `kat_base + 0x2000`, `rom_base`) fault. (Do not probe `[rom_end - 0x20, rom_end)` while mapped because it lies inside the 8 KiB NAPOT window and holds ECC-poisoned `rom_ctrl` digest words.)
4. **KAT validation and execution:** validates the `"FKAT"` descriptor table header against `kFipsKatMaxTableSize` (`0x1F80`) and runs all 31 KAT operations (across 30 descriptor entries) via `otcrypto` and silicon creator drivers with OTTF alert monitoring enabled.
5. **Immediate revocation:** clears ePMP slot 0 and confirms loads from `kat_base` and `rom_base + rom_size - 0x20` once again raise `LoadAccessFault`.

## Running the Tests

Use `bazelisk` (or the repository wrapper `./bazelisk.sh`) from the repository root:

### Host Unit Test (with UBSan)

Validates descriptor table invariants, bounds/alignment/overflow rejection, fixed 16-byte sparse signature unpacking, and all 30 embedded entries in `kFipsKatRomBlob`:

```sh
bazelisk test --config=ubsan //sw/device/silicon_creator/rom:fips_kat_table_unittest
```

### CW340 FPGA E2E Test

Runs the full transient ePMP isolation probes and all 31 KAT operations (30 ROM entries) on a CW340 FPGA board:

```sh
bazelisk test //sw/device/silicon_creator/rom/e2e/kat:fips_kat_rom_test_fpga_cw340_rom_ext
```

## ROM Blob Footprint and Covered Algorithms

The combined ROM blob (`kFipsKatRomBlob`, `sizeof(fips_kat_rom_blob_t)`) is **7,448 B (`0x1D18`, ~7.3 KiB)**, leaving **616 B** free before `.chip_info` (`0x6FF80`) inside the 8,064 B usable window:

- **Descriptor table (`256 B`):** `16 B` root header (`magic`, `version`, `entry_count`, `total_size`) + `30 x 8 B` `fips_kat_entry_t` entries (`uint16_t algorithm_id, reserved, offset, size`).
- **Vector payloads (`7,192 B`):** uniform `uint16_t` payload length headers with 4-byte aligned sub-fields (`FIPS_KAT_ALIGN4`).

| ID | Algorithm | Schema | Size (B) |
| :-: | :--- | :--- | --: |
| 1 | SHA2-256 | `hmac_kat_data_t` | 44 |
| 2 | SHA2-512 | `hmac_kat_data_t` | 76 |
| 3 | HMAC-SHA2-256 | `hmac_kat_data_t` | 124 |
| 4 | HMAC-SHA2-512 | `hmac_kat_data_t` | 188 |
| 5 | SHAKE-256 | `hmac_kat_data_t` | 44 |
| 6 | KMAC-256 | `kdf_kat_data_t` | 132 |
| 7 | AES-256-ECB (Decrypt/Encrypt) | `aes_kat_data_t` | 76 |
| 8 | AES-256-CBC (2-block Decrypt/Encrypt) | `aes_kat_data_t` | 124 |
| 9 | AES-256-KWP (Wrap/Unwrap) | `aes_kat_data_t` | 80 |
| 10 | KDF-CTR-HMAC-SHA2-256 | `kdf_kat_data_t` | 108 |
| 11 | KDF-KMAC-256 | `kdf_kat_data_t` | 120 |
| 12 | RSA-2048 Verify (PKCS#1 v1.5 SHA-256) | `asymmetric_verify_kat_data_t` | 544 |
| 13 | RSA-4096 Sign & Verify (`kFipsKatAlgRsa4096`, PKCS#1 v1.5 SHA-512) | `asymmetric_sign_kat_data_t` | 1,568 |
| 14 | *Reserved (merged into ID 13)* | -- | -- |
| 15 | ECDSA P-256 Sign | `asymmetric_sign_kat_data_t` | 268 |
| 16 | ECDSA P-256 Verify | `asymmetric_verify_kat_data_t` | 268 |
| 17 | ECDSA P-384 Sign | `asymmetric_sign_kat_data_t` | 332 |
| 18 | ECDSA P-384 Verify | `asymmetric_verify_kat_data_t` | 332 |
| 19 | Ed25519 Sign | `asymmetric_sign_kat_data_t` | 112 |
| 20 | Ed25519 Verify | `asymmetric_verify_kat_data_t` | 112 |
| 21 | ECDH P-256 | `ecdh_kat_data_t` | 136 |
| 22 | ECDH P-384 | `ecdh_kat_data_t` | 200 |
| 23 | X25519 | `ecdh_kat_data_t` | 104 |
| 24 | ML-DSA-87 (5 ACVP rejection cases: DKG/Sign/Verify) | `mldsa_kat_data_t` | 484 |
| 25 | ML-KEM-1024 (DKG/Encaps/Decaps) | `kem_kat_data_t` | 204 |
| 26 | CTR_DRBG AES-256 (SP 800-90A Sec. 11.3) | `drbg_kat_data_t` | 472 |
| 27 | Entropy Source SHA3-384 Conditioning | `hmac_kat_data_t` | 104 |
| 28 | AES-256-GCM (Encrypt/Decrypt) | `aes_kat_data_t` | 192 |
| 29 | FIPS 205 SLH-DSA-SHA2-128s / SPHINCS+-SHA2-128s-simple Verify (sparse) | `sparse_verify_kat_data_t` | 384 |
| 30 | HKDF-SHA2-384 (Extract/Expand) | `hkdf_kat_data_t` | 200 |
| 31 | SHA2-384 | `hmac_kat_data_t` | 60 |

*Notes:*
- **ID 13 (`kFipsKatAlgRsa4096`):** Combines RSA-4096 Sign and Verify in a single NIST CAVP keypair entry (`priv_key = N || D` [1,024 B], `ephemeral = e = 65537` [4 B LE], `msg = "Test message."` [13 B, `pad4=16 B`], `sig1 = S` [512 B]). ID 14 is reserved.
- **ID 29 (`kFipsKatAlgSphincsPlusSha2_128sVerify`):** Encodes the 7,856-byte FIPS 205 `SLH-DSA-SHA2-128s` pure-mode (`ctx = ""`) signature as 17 fixed 16-byte `fips_kat_sparse_chunk_t` records (`20 B` each at 16-byte-aligned offsets, `384 B` total; 261 non-zero signature bytes / 278 non-zero bytes total), verified with `fips_kat_sparse_verify_expected_size()` and unpacked via `fips_kat_sparse_sig_unpack()`, saving 7,560 B compared to a raw 7,944 B payload.
