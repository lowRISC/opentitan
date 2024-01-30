# Contribution Guidelines for the OT Cryptolib

This guide is for contributors to the OT cryptolib (the code under `sw/device/lib/crypto`) and outlines some general coding guidelines.

## Style and Naming

- Cryptolib code should follow the [C style guide](../../contributing/style_guides/c_cpp_coding_style.md) and the [OTBN style guide](../../contributing/style_guides/otbn_style_guide.md).
- All definitions in the top-level API should be prefixed with `otcrypto`.
- Unit tests should be named after the files they test, e.g. the test for `foo.c` would be `foo_unittest.cc`.

## Code organization

- The top-level cryptolib API is under `sw/device/lib/crypto/include`. This API should be kept as stable as possible.
- If modifying the top-level API, update the [documentation](cryptolib_api.md).
- The drivers and their tests are under `sw/device/lib/crypto/drivers`.
- All other code is under `sw/device/lib/crypto/impl`.
- Unit tests are typically stored in the same directory as the code they test.
- Device-side test code is under `sw/device/tests/crypto`.
- Host-side test code is under `sw/host/cryptotest`.

## Hardening

- Harden sensitive control flow with `HARDENED_CHECK_EQ` and similar.
- Use word-aligned values wherever possible.
- Use multi-bit booleans for sensitive control flow: `kHardenedBoolTrue` and `kHardenedBoolFalse`.
- For sensitive value comparisons, use `hardened_memeq`.
- Use `hardened_memshred` to clear any sensitive values that are no longer needed.
- Turn icache off for code that needs to be constant-time.

See `sw/device/lib/base/hardened.h` for more details about how to use hardening macros.

## Module IDs

- Use `grep -Ir MODULE_ID sw/device/lib/crypto/` to see existing IDs.
- Add a unique `MODULE_ID` statement to the top of all `.c` files under `sw/device/lib/crypto` that include any `OTCRYPTO` error codes.
- Pay attention to any pattern for module IDs in a given directory and try to be consistent. For example, some directories have module IDs that all begin with the same leter.
- Test `.c` files that will never be imported by anything else can have the module ID "tst".

Module IDs will show up in error codes when you run tests with `--define crypto_status_debug=true`.
See the [status codes](#status-codes) section for more details.

## Status Codes

- All functions in the top-level API (`sw/device/lib/crypto/include`) should return `otcrypto_status_t`.
- All internal functions should return either `void` or `status_t`.
- Functions returning `status_t` or `otcrypto_status_t` should always return one of the codes defined in `sw/device/lib/crypto/impl/status.h`, e.g. `OTCRYPTO_RECOV_ERR`.
- Always use `HARDENED_TRY` instead of `TRY` when checking if an internal function succeeded. `TRY` is OK for tests.
- Prefix all function declarations that return `status_t` or `otcrypto_status_t` with `OT_WARN_UNUSED_RESULT`.

### Background

#### Specialized status codes

The cryptolib status code `otcrypto_status_t` is bit-compatible with `status_t`, but the error values are always the same.
Typically, `status_t` would display the module ID and line number to help debugging, but since this information could theoretically help an attacker we do not want to expose it.
However, this makes debugging errors in tests painful, since there are only a few possible error codes.

To solve that problem, we use the specialized error macros `OTCRYPTO_RECOV_ERR`, `OTCRYPTO_BAD_ARGS`, etc.
These macros are defined differently depending on the `OTCRYPTO_STATUS_DEBUG` define:
- if `OTCRYPTO_STATUS_DEBUG` is defined, the error codes behave like `status_t` and provide module IDs and line numbers
- if `OTCRYPTO_STATUS_DEBUG` is not defined, the error codes are simply a few constant values as defined by the `otcrypto_status_value_t` enum.

You can pass `--define crypto_status_debug=true` to set the `OTCRYPTO_STATUS_DEBUG` flag via Bazel.
See `sw/device/lib/crypto/impl/status.h` for more details, and see [opentitan#17803](https://github.com/lowRISC/opentitan/issues/17803) for the historical discussion.

#### Using `HARDENED_TRY`

The `TRY` macro only checks that the single "error" bit is not set.
Since this would be vulnerable to fault attacks, the `HARDENED_TRY` macro checks specifically for the `kHardenedBoolTrue` value and fails if it gets anything else, even if the error bit is false.

#### Using `OT_WARN_UNUSED_RESULT`

This macro protects against a caller forgetting to check and forward the error code.
It produces a compile-time warning.

### Examples

Header file (top-level API):
```c
/**
 * Example top-level API function.
 *
 * @param foo An input value.
 * @param[out] bar An output value.
 * @return Status code: OK or error.
 */
OT_WARN_UNUSED_RESULT
otcrypto_status_t otcrypto_process_foo(otcrypto_byte_buf_t foo, otcrypto_word32_buf_t bar);
```

Header file (internal function):
```c
/**
 * Example internal function.
 *
 * @param baz An input value.
 * @param[out] bar An output value.
 * @return Status code: OK or error.
 */
OT_WARN_UNUSED_RESULT
status_t baz_to_bar(uint32_t baz, otcrypto_word32_buf_t bar);
```

Implementation:
```c
/**
 * Example internal static function.
 *
 * @param foo An input value.
 * @param[out] baz An output value.
 * @return Status code: OK or error.
 */
OT_WARN_UNUSED_RESULT
static status_t foo_to_baz(otcrypto_byte_buf_t foo, uint32_t baz) {
  // do something ...
  return OTCRYPTO_OK;
}

otcrypto_status_t otcrypto_process_foo(otcrypto_byte_buf_t foo, otcrypto_word32_buf_t bar) {
  // Check some basic error conditions.
  if ((foo.data == NULL && foo.len != 0) || bar.data == NULL) {
    return OTCRYPTO_BAD_ARGS;
  }

  // Call the internal function and check the result.
  uint32_t baz;
  HARDENED_TRY(foo_to_baz(foo, baz));

  // Call another internal function and directly return the result.
  return baz_to_bar(baz, bar);
}
```
