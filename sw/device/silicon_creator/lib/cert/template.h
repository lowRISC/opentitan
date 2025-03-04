// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_CERT_TEMPLATE_H_
#define OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_CERT_TEMPLATE_H_

#include "sw/device/lib/base/macros.h"
#include "sw/device/lib/base/memory.h"
#include "sw/device/silicon_creator/lib/error.h"

#ifdef __cplusplus
extern "C" {
#endif

/**
 * Structure holding the state of the template engine.
 *
 * The fields in this structure should be considered
 * private and not be read or written directly.
 *
 * The following diagram shows the pointers location during encoding.
 * Takes Cdi0 TBS as as example:
 *
 * Template Const Bytes:
 *   `kTemplateConstBytes[]`  `const_end`     `+ sizeof(kTemplateConstBytes)`
 *   | Bytes Copied to Output     |         Unconsumed Template Const Bytes |
 *
 * `const_end` pointer will start from offset zero, and increase to
 * `sizeof(kTemplateConstBytes)` at the end of encoding.
 *
 * Output Buffer:
 *   `out_begin`    `out_end`    `+ kCdi0MaxTbsSizeBytes`
 *   | Used Bytes       |        Remaining Unused Space |
 *
 * `out_begin` pointer will not change.
 * `out_end` pointer starts from `out_begin` to the actual output size.
 * The actual size is between [kCdi0MinTbsSizeBytes, kCdi0MaxTbsSizeBytes].
 */
typedef struct template_state {
  // Points to the remaining pre-computed const array from codegen.
  const uint8_t *const_end;
  // Points to the original start of the output buffer.
  const uint8_t *out_begin;
  // Points to the end of bytes already outputted.
  uint8_t *out_end;
} template_state_t;

/**
 * Pointer to a specific output location.
 */
typedef void *template_pos_t;

/**
 * Initialize the template engine.
 *
 * @param state Pointer to the template engine state.
 * @param out_buf Pointer to a user-provided output buffer.
 * @param const_bytes Pointer to a pre-generated template bytes.
 */
static inline void template_init(template_state_t *state, uint8_t *out_buf,
                                 const uint8_t *const_bytes) {
  state->out_begin = state->out_end = out_buf;
  state->const_end = const_bytes;
}

/**
 * Finalize template engine and set the actual output size.
 *
 * @param state Pointer to the template engine state.
 * @return The generated size in bytes.
 */
static inline uint16_t template_finalize(template_state_t *state) {
  return (uint16_t)(state->out_end - state->out_begin);
}

/**
 * Set the `value` to the `bit_offset` bit of previous `byte_offset` byte.
 *
 * This function assume the corresponding bit is zero before calling, which
 * is ensured by the template code generator.
 *
 * @param state Pointer to the template engine state.
 * @param byte_offset Number of bytes before the last output bytes.
 * @param bit_offset Index of the bit to be set.
 * @param value Set the bit to one when true.
 */
static inline void template_set_bit(template_state_t *state, int byte_offset,
                                    int bit_offset, bool value) {
  *(state->out_end - byte_offset) |= ((uint8_t) !!value) << bit_offset;
}

/**
 * Output a ASN1 DER boolean.
 *
 * @param state Pointer to the template engine state.
 * @param val Value to be output.
 */
static inline void template_push_asn1_bool(template_state_t *state, bool val) {
  *state->out_end = val ? 0xff : 0x00;
  state->out_end += 1;
}

/**
 * Private implementation of `template_push_hex`.
 *
 * @param out Pointer to the output buffer.
 * @param inp Pointer to a byte array.
 * @param size Number of the bytes in the array.
 * @return the new end of the output buffer.
 */
uint8_t *template_push_hex_impl(uint8_t *out, const uint8_t *inp, size_t size);

/**
 * Output the buffer as a hex-encoded string.
 *
 * @param state Pointer to the template engine state.
 * @param buf Pointer to a byte array.
 * @param size Number of the bytes in the array.
 */
static inline void template_push_hex(template_state_t *state,
                                     const uint8_t *buf, size_t size) {
  state->out_end = template_push_hex_impl(state->out_end, buf, size);
}

/**
 * Output the buffer as raw bytes.
 *
 * @param state Pointer to the template engine state.
 * @param buf Pointer to a byte array.
 * @param size Number of the bytes in the array.
 */
static inline void template_push_bytes(template_state_t *state,
                                       const uint8_t *buf, size_t size) {
  memcpy(state->out_end, buf, size);
  state->out_end += size;
}

/**
 * Output `size` bytes from the pre-generated template.
 *
 * @param state Pointer to the template engine state.
 * @param size Number of the bytes to output.
 */
static inline void template_push_const(template_state_t *state, size_t size) {
  memcpy(state->out_end, state->const_end, size);
  state->out_end += size;
  state->const_end += size;
}

/**
 * Private implementation of `template_asn1_integer`.
 *
 * @param out Pointer to the output buffer.
 * @param tag Identifier octet of the tag.
 * @param tweak_msb Set the MSB before encoding when true.
 * @param bytes_be Pointer to a byte array holding an integer in big-endian
 * format.
 * @param size Size of the `bytes_be` array in bytes.
 * @return the new end of the output buffer.
 */
uint8_t *template_asn1_integer_impl(uint8_t *out, uint8_t tag, bool tweak_msb,
                                    const uint8_t *bytes_be, size_t size);

/**
 * Output a tagged integer.
 *
 * This function allows the caller to set the tag to a non-standard value which
 * can be useful for IMPLICIT integers. Use ASN1_TAG_INTEGER for standard
 * integers.
 *
 * @param state Pointer to the template engine state.
 * @param tag Identifier octet of the tag.
 * @param tweak_msb Set the MSB before encoding when true.
 * @param bytes_be Pointer to a byte array holding an integer in big-endian
 * format.
 * @param size Size of the `bytes_be` array in bytes.
 */
static inline void template_asn1_integer(template_state_t *state, uint8_t tag,
                                         bool tweak_msb,
                                         const uint8_t *bytes_be, size_t size) {
  state->out_end = template_asn1_integer_impl(state->out_end, tag, tweak_msb,
                                              bytes_be, size);
}

/**
 * U32 version of the `template_asn1_integer`.
 *
 * @param state Pointer to the template engine state.
 * @param tag Identifier octet of the tag.
 * @param tweak_msb Set the MSB before encoding when true.
 * @param value Integer value.
 */
static inline void template_asn1_uint32(template_state_t *state, uint8_t tag,
                                        bool tweak_msb, uint32_t value) {
  uint32_t _value = __builtin_bswap32(value);
  state->out_end = template_asn1_integer_impl(state->out_end, tag, tweak_msb,
                                              (uint8_t *)&_value, 4);
}

/**
 * Memorize a location to be patched with the actual output size.
 *
 * The function will saved the address (last output byte + offset) for
 * patching later, and it should be paired with a `template_patch_size_*`.
 *
 * @param state Pointer to the template engine state.
 * @param offset Number of bytes after the last output byte.
 * @return the memorized location for calling `template_patch_size_be`.
 */
static inline template_pos_t template_save_pos(template_state_t *state,
                                               ptrdiff_t offset) {
  return (template_pos_t *)(state->out_end + offset);
}

/**
 * Private implementation of `template_patch_size_be`.
 */
void template_patch_size_be_impl(template_pos_t memo, uint8_t *out_end);

/**
 * Add the actual output size after the memo to the patch location.
 *
 * The function will perform addition as BE u16 (i.e. mod 65536).
 *
 * @param state Pointer to the template engine state.
 * @param memo The memorized location from `template_save_pos`.
 */
static inline void template_patch_size_be(template_state_t *state,
                                          template_pos_t memo) {
  template_patch_size_be_impl(memo, state->out_end);
}

/**
 * Helpers for writing static assertions on variable array sizes.
 */
#define ASSERT_VAR_SIZE_EQ(actual, expected) \
  static_assert(actual == expected, "Invalid variable size.");

#define ASSERT_VAR_SIZE_GE(actual, expected) \
  static_assert(actual >= expected, "Invalid variable size.");

#define ASSERT_VAR_SIZE_LE(actual, expected) \
  static_assert(actual <= expected, "Invalid variable size.");

/**
 * Check if the given variable is fixed-length.
 *
 * @param template The name defined in the hjson template in upper camel case.
 * @param field The variable name in upper camel case.
 */
#define TEMPLATE_ASSERT_FIXED_LENGTH(template, field)    \
  ASSERT_VAR_SIZE_EQ(k##template##Min##field##SizeBytes, \
                     k##template##Max##field##SizeBytes);

/**
 * Check if the given size is within the range defined in the template.
 *
 * @param template The name defined in the hjson template in upper camel case.
 * @param field The variable name in upper camel case.
 * @param size The size of the variable value in bytes.
 */
#define TEMPLATE_CHECK_SIZE(template, field, size)                \
  ASSERT_VAR_SIZE_GE((size), k##template##Min##field##SizeBytes); \
  ASSERT_VAR_SIZE_LE((size), k##template##Max##field##SizeBytes);

/**
 * Set a template variable value and check its size.
 *
 * @param params Pointer to the generated *_values_t variable.
 * @param template The name defined in the hjson template in upper camel case.
 * @param field The variable name in upper camel case.
 * @param value The value to set. It should be typed as a fixed size value.
 */
#define TEMPLATE_SET(params, template, field, value)      \
  do {                                                    \
    TEMPLATE_CHECK_SIZE(template, field, sizeof(value));  \
    (params).k##template##Field##field = (void *)(value); \
  } while (0)

/**
 * Set a template variable with the value array truncated to `size`.
 *
 * @param params Pointer to the generated *_values_t variable.
 * @param template The name defined in the hjson template in upper camel case.
 * @param field The variable name in upper camel case.
 * @param value The value to set. It should be typed as a fixed size value.
 * @param size The size after truncated.
 */
#define TEMPLATE_SET_TRUNCATED(params, template, field, value, size) \
  do {                                                               \
    ASSERT_VAR_SIZE_GE(sizeof(value), size);                         \
    TEMPLATE_CHECK_SIZE(template, field, size);                      \
    (params).k##template##Field##field = (void *)(value);            \
  } while (0)

#ifdef __cplusplus
}  // extern "C"
#endif  // __cplusplus

#endif  // OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_CERT_TEMPLATE_H_
