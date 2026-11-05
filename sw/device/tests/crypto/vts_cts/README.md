# Crypto VTS/CTS Compliance Test Suite

This directory contains device-side tests exercising `otcrypto` against test
vectors and edge cases derived from the Android Compatibility Test Suite (CTS)
and Vendor Test Suite (VTS):

- `aes_vts_cts_test.c`: AES-ECB, AES-CBC, and AES-CTR KATs, padding checks,
  multi-block stepping patterns, and 0-byte unpadded inputs.
- `aes_gcm_vts_cts_test.c`: AES-GCM KATs, streaming chunk patterns, AAD ordering,
  and 96-bit / 128-bit tags.
- `tdes_vts_cts_test.c`: TDES-ECB and TDES-CBC KATs, PKCS#7 padding checks, and
  0-byte unpadded inputs.
- `ecc_mac_vts_cts_test.c`: P-256 ECDSA, P-256 ECDH (32-byte and 64-byte shared
  secrets), and HMAC (including truncated output tags).
- `rsa_vts_cts_test.c`: RSA-2048 PKCS#1 v1.5, PSS, OAEP (including independent
  MGF1 digests), and raw RSA.

## Wrapper Requirements for Full Compliance

Several VTS/CTS test cases enforce policy rules, streaming state management, or
byte-level wire formatting that live in the caller/wrapper layer above
`otcrypto`. Cases that require caller policy checks or pre-padding before
invoking `otcrypto` (items 1, 2, 5, and 6) are noted in comments in `test_main()`,
items 3, 4, 7, and 9 are exercised directly in `test_main()`, and items 8 and 10
describe streaming and wire-encoding duties of a KeyMint/JCA wrapper.

To pass the full VTS/CTS suite through a wrapper layer, the wrapper must handle
the following responsibilities:

### 1. AES-GCM Minimum Tag Length (`AesGcmMinMacOutOfRange`, `AesGcmTooShortTag`)
- **File**: `aes_gcm_vts_cts_test.c` (noted in `test_main()`)
- **Requirement**: `otcrypto` supports 32-bit and 64-bit GCM tags
  (`kOtcryptoAesGcmTagLen32`, `kOtcryptoAesGcmTagLen64`). The wrapper must
  reject tag lengths shorter than 96 bits before invoking
  `otcrypto_aes_gcm_encrypt` or `otcrypto_aes_gcm_decrypt`.

### 2. AES-CTR Padding Mode Check (`AesCtrIncompatiblePaddingMode`)
- **File**: `aes_vts_cts_test.c` (noted in `test_main()`)
- **Requirement**: When operating in `kOtcryptoAesModeCtr`, the wrapper must
  reject any padding mode other than `kOtcryptoAesPaddingNull` before invoking
  `otcrypto_aes`.

### 3. Hashed vs. Unhashed ECDSA & RSA Signing/Verification (`ecdsa_p256_hash_null_mode_test`, `rsa_vts_signing_no_digest_and_raw_test`)
- **File**: `ecc_mac_vts_cts_test.c`, `rsa_vts_cts_test.c` (active in `test_main()`)
- **Requirement**: Both ECDSA and RSA use `otcrypto_ecdsa_p256_sign_verify` /
  `otcrypto_ecdsa_p256_verify` and `otcrypto_rsa_sign` / `otcrypto_rsa_verify`
  with an `otcrypto_hash_digest_t`:
  - **Hashed modes (e.g., `Digest::SHA_2_256`)**: The wrapper hashes the message
    first via `otcrypto_sha2_256` (or `otcrypto_sha2_init` / `update` / `final`
    for streaming `update()` calls) and passes the resulting digest with
    `digest.mode = kOtcryptoHashModeSha256`.
  - **Unhashed ECDSA (`Digest::NONE` / `NONEwithECDSA`)**: The wrapper formats
    the raw big-endian message into a `kP256CoordWords` (32-byte) buffer
    (truncating inputs longer than 32 bytes to the leftmost 32 bytes, or
    right-aligning shorter inputs with leading zero bytes, without byte-reversing)
    and passes `digest.mode = kOtcryptoHashModeNull`.
  - **Unhashed RSA PKCS#1 v1.5 (`Digest::NONE` / `NONEwithRSA`)**: For unhashed
    messages up to $k - 11 = 245$ bytes (including 0-byte and non-word-aligned
    messages such as the 23-byte `kCtsSigMsg` KAT), the wrapper copies the
    big-endian message bytes into a word-aligned `uint32_t` buffer (or `NULL`
    when `len == 0`), sets `digest.len = byte_len` (in bytes), and calls
    `otcrypto_rsa_sign` / `otcrypto_rsa_verify` with `kOtcryptoRsaPaddingPkcs`
    and `digest.mode = kOtcryptoHashModeNull`.

### 4. RSA-OAEP MGF1 Digest Selection (`rsa_cts_oaep_sha256_mgf1_sha1_kat_test`)
- **File**: `rsa_vts_cts_test.c` (active in `test_main()`)
- **Requirement**: When the OAEP MGF1 hash differs from the main label digest
  `hash_mode`, the wrapper must set the RSA key mode to
  `kOtcryptoKeyModeRsaEncryptOaepMgfSha1` or
  `kOtcryptoKeyModeRsaEncryptOaepMgfSha256` instead of
  `kOtcryptoKeyModeRsaEncryptOaep`.

### 5. Raw RSA Short Inputs and All-Zero Boundary (`RsaNoPaddingShortMessage`, `RsaTooShortMessage`)
- **File**: `rsa_vts_cts_test.c` (noted in `test_main()`)
- **Requirement**:
  - **Short non-zero inputs (`< modulus size`)**: `otcrypto` requires raw RSA
    encryption and signing inputs to match the full modulus size (`num_bytes` /
    `num_words`). The wrapper must left-pad short big-endian inputs with leading
    `0x00` bytes to the full modulus byte length before converting to `otcrypto`'s
    little-endian word format.
  - **All-zero raw RSA plaintext (`m = 0` or 0-byte `EmptyArray.BYTE`)**:
    `otcrypto` (`run_rsa.c`) intentionally rejects all-zero modexp outputs
    (`0^e mod n == 0`) with `OTCRYPTO_BAD_ARGS` as a fault/safety check. If a
    caller API requires `RSA/ECB/NoPadding` on `m = 0` to return `0`, the wrapper
    must handle the all-zero boundary case directly.

### 6. Symmetric Two-Step PKCS#7 Padding on Encrypt and Decrypt
- **File**: `aes_vts_cts_test.c`, `tdes_vts_cts_test.c` (active in `test_main()`)
- **Requirement**: `otcrypto_aes` and `otcrypto_tdes` require caller-allocated
  block-multiple output buffers (`cipher_output->len`) and decouple block
  decryption from constant-time padding validation:
  - **Encrypt**: Call `otcrypto_aes_padded_plaintext_length` (or
    `otcrypto_tdes_padded_plaintext_length`) to compute the padded output length,
    then call `otcrypto_aes` / `otcrypto_tdes` with `kOtcryptoAesPaddingPkcs7` /
    `kOtcryptoTdesPaddingPkcs7`.
  - **Decrypt**: Call `otcrypto_aes` / `otcrypto_tdes` with
    `kOtcryptoAesPaddingPkcs7` / `kOtcryptoTdesPaddingPkcs7` to decrypt all blocks,
    then call `otcrypto_aes_padding_strip` / `otcrypto_tdes_padding_strip` to
    validate and strip the padding in constant time.

### 7. Block-Aligned Streaming (`update()` / `finish()`) for AES and TDES
- **File**: `aes_vts_cts_test.c`, `tdes_vts_cts_test.c` (wrapper responsibility)
- **Requirement**: `otcrypto_aes` and `otcrypto_tdes` operate on complete 16-byte
  (AES) or 8-byte (TDES) blocks (`AES-CTR` accepts non-multiple-of-16 lengths in
  a single-shot call or on the final `finish()` chunk, as `otcrypto_aes` advances
  `iv` by `ceil_div(len, 16)` whole 16-byte blocks per call). To support arbitrary
  streaming chunk sizes (such as 1-byte `update()` calls), the wrapper must
  maintain a 16-byte (AES-ECB, AES-CBC, AES-CTR) or 8-byte (TDES-ECB, TDES-CBC)
  block buffer across `update()` calls—and when decrypting with PKCS#7 padding,
  hold back the final full block until `finish()` so that
  `otcrypto_*_padding_strip` is applied only to the terminal block.

### 8. P-256 ECDH Shared Secret Key Mode, Per-Share Byte Reversal for HKDF, and Unmasking (`ecdh_p256_vts_test`, `ecdh_p256_32b_shared_secret_vts_test`)
- **File**: `ecc_mac_vts_cts_test.c` (active in `test_main()`)
- **Requirement**: `otcrypto_ecdh_p256` takes asymmetric `kOtcryptoKeyModeEcdhP256`
  keys as inputs, but writes the output shared secret in Boolean (XOR) shares
  in little-endian word order into `shared_secret->keyblob` via
  `keyblob_from_shares`. Because `kOtcryptoKeyTypeEcc` adds 64 redundant bits
  (8 bytes) per share for arithmetic scalar shares, the wrapper must configure
  `shared_secret->config.key_mode` with a **symmetric** key mode (e.g.,
  `kOtcryptoKeyModeAesCtr` or `kOtcryptoKeyModeHmacSha256`) and
  `key_length = 32` (for the 32-byte $x$-coordinate) or `64` (for $(x, y)$):
  - **Feeding into `otcrypto_hkdf` (or symmetric primitives) without unmasking**:
    Because byte reversal commutes with XOR masking
    ($\text{reverse}(\text{share}_0) \oplus \text{reverse}(\text{share}_1) = \text{reverse}(x_S) = Z$),
    the wrapper can export the two Boolean shares, byte-reverse each 32-byte
    share independently (`share_be[i] = __builtin_bswap32(share_le[7 - i])`)
    without ever unmasking $x_S$, and re-import them via
    `otcrypto_import_blinded_key` before calling `otcrypto_hkdf`.
  - **Returning raw 32-byte shared secret (e.g., KeyMint `AGREE_KEY`)**: The
    wrapper unmasks the two Boolean shares (`share0 ^ share1`) and reverses the
    32 bytes from little-endian to big-endian.

### 9. Endianness and Wire-Format Encoding Across APIs
- **File**: `ecc_mac_vts_cts_test.c`, `rsa_vts_cts_test.c` (wrapper responsibility)
- **Requirement**:
  - **Big-Endian / Native Byte Order** (`AES`, `AES-GCM`, `TDES`, `HMAC`, `SHA-2`,
    `HKDF`, RSA PKCS#1 v1.5 (`kOtcryptoKeyModeRsaEncryptPkcs`) and RSA-OAEP
    `label`/`plaintext` byte buffers, and `message_digest.data` for **P-256 ECDSA
    `Digest::NONE`** and **RSA PKCS#1 v1.5 `Digest::NONE`**): Passed in
    big-endian byte order without byte reversal (for `Digest::NONE` in ECDSA and
    PKCS#1 v1.5, `p256.c` and `rsa_padding.c` reverse the bytes internally).
  - **Little-Endian `uint32_t` Word Order** (`RSA` modulus `n`, private exponent
    `d`, signature, ciphertext, raw RSA (`kOtcryptoKeyModeRsaRaw`)
    `otcrypto_rsa_encrypt` / `decrypt` plaintext, and raw RSA
    (`kOtcryptoRsaPaddingNull`) `message_digest.data`; `P-256` affine coordinates
    `(x, y)`, private scalar `d`, ECDSA `(r, s)`, and ECDH shared secret): The
    wrapper must reverse big-endian wire-format byte arrays to/from little-endian
    words and ASN.1 DER encode/decode ECDSA signatures
    (`SEQUENCE { INTEGER r, INTEGER s }`).
