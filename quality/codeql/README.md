<!--
Copyright lowRISC contributors (OpenTitan project).
Licensed under the Apache License, Version 2.0, see LICENSE for details.
SPDX-License-Identifier: Apache-2.0
-->

# OpenTitan CodeQL Static Analysis

This directory contains custom CodeQL queries (`.ql` files) for the OpenTitan project.

## Overview
OpenTitan uses GitHub's CodeQL engine to run static analysis on C/C++ code. Currently, only `cryptolib` (`//sw/device/lib/crypto:otcrypto`) and its tests (`//sw/device/tests/crypto/...`) are built and scanned; the rest of the codebase is not yet covered.

The GitHub Actions workflow (`.github/workflows/codeql.yml`) traces the `cryptolib` build and runs CodeQL's `security-and-quality` suite alongside the custom OpenTitan queries in this directory.

## Custom Queries
Because CodeQL's built-in C/C++ queries do not track buffer capacities across OpenTitan's custom buffer/key structs or randomized word-loop helpers (`hardened_memcpy`, `hardened_memshred`), we include lightweight queries targeting stable `cryptolib` primitives:

- `opentitan_crypto_bounds.ql`: Checks static memory capacities (arrays, struct field arrays, `&struct` / `&scalar` addresses, and constant offsets) against declared or accessed lengths across:
  - **Public `otcrypto` buffer and key structs**: `otcrypto_byte_buf_t`, `otcrypto_const_byte_buf_t`, `otcrypto_word32_buf_t`, `otcrypto_const_word32_buf_t`, `otcrypto_generic_buf_t`, `otcrypto_hash_digest_t`, `otcrypto_blinded_key_t`, and `otcrypto_unblinded_key_t` (checked on initializers including `OTCRYPTO_MAKE_BUF`, field assignments, constructor helpers, and dual-share `keyblob` copies).
  - **Foundational memory and OTBN DMEM primitives**: Automatically discovers all `(ptr, ..., size_t len)` functions declared in `sw/device/lib/base/hardened_memory.h` and `sw/device/lib/base/memory.h` (`hardened_*`, `randomized_*`, `consttime_*`, `memcpy`/`ot_memcpy`, `memset`/`ot_memset`, `memcmp`/`ot_memcmp`, etc.) alongside `otbn_dmem_write` and `otbn_dmem_read`, so new memory helpers added to those headers are covered automatically.
- `opentitan_crypto_const_mutation.ql`: Flags casting away `const` on any `const` struct field in `sw/device/lib/crypto/` when the resulting pointer remains non-`const`.
- `opentitan_crypto_share_wipe.ql`: Flags functions in `sw/device/lib/crypto/` that shred one `<prefix>0` / `<prefix>1` share field of a struct with `hardened_memshred` without wiping its paired field or the whole struct.
