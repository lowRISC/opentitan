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
 * Initialize the template engine.
 *
 * @param out_buf Pointer to a user-provided output buffer.
 * @param const_bytes Pointer to a pre-generated template bytes.
 */
#define template_init(out_buf, const_bytes)  \
  const uint8_t *_ptr_const = (const_bytes); \
  const uint8_t *const _ptr_org = (out_buf); \
  uint8_t *_ptr_out = (out_buf);

/**
 * Finalize template engine and set the actual output size.
 *
 * @param ptr_size Pointer to a user-provided size variable.
 */
#define template_finalize(ptr_size) \
  *(ptr_size) = (uint16_t)(_ptr_out - _ptr_org);

/**
 * Set the `bit_offset` bit of previous `byte_offset` byte.
 *
 * @param byte_offset Number of bytes before the last output bytes.
 * @param bit_offset Index of the bit to be set.
 * @param value Value of the bit.
 */
#define template_set_bit(byte_offset, bit_offset, value) \
  { *(_ptr_out - (byte_offset)) |= ((uint8_t) !!(value)) << (bit_offset); }

/**
 * Output a ASN1 DER boolean.
 *
 * @param val Value to be output.
 */
#define template_push_asn1_bool(val) \
  {                                  \
    *_ptr_out = (val) ? 0xff : 0x00; \
    _ptr_out += 1;                   \
  }

/**
 * Output the buffer as a hex-encoded string.
 *
 * @param buf Pointer to a byte array.
 * @param size Number of the bytes in the array.
 */
#define template_push_hex(buf, size)               \
  {                                                \
    template_push_hex_impl(_ptr_out, buf, (size)); \
    _ptr_out += (size)*2;                          \
  }

void template_push_hex_impl(uint8_t *out, const uint8_t *inp, size_t size);

/**
 * Output the buffer as raw bytes.
 *
 * @param buf Pointer to a byte array.
 * @param size Number of the bytes in the array.
 */
#define template_push_bytes(buf, size) \
  {                                    \
    memcpy(_ptr_out, buf, (size));     \
    _ptr_out += (size);                \
  }

/**
 * Output `size` bytes from the pre-generated template.
 *
 * @param size Number of the bytes to output.
 */
#define template_push_const(size)         \
  {                                       \
    memcpy(_ptr_out, _ptr_const, (size)); \
    _ptr_out += (size);                   \
    _ptr_const += (size);                 \
  }

/**
 * Output a tagged integer.
 *
 * This function allows the caller to set the tag to a non-standard value which
 * can be useful for IMPLICIT integers. Use ASN1_TAG_INTEGER for standard
 * integers.
 *
 * @param tag Identifier octet of the tag.
 * @param bytes_be Pointer to a byte array holding an integer in big-endian
 * format.
 * @param value Integer value.
 */
#define template_asn1_integer(tag, tweak_msb, bytes_be, size)           \
  {                                                                     \
    _ptr_out = template_asn1_integer_impl(_ptr_out, (tag), (tweak_msb), \
                                          (bytes_be), (size));          \
  }

/**
 * U32 version of the `template_asn1_integer`.
 *
 * @param tag Identifier octet of the tag.
 * @param value Integer value.
 */
#define template_asn1_uint32(tag, tweak_msb, value)                     \
  {                                                                     \
    uint32_t _value = __builtin_bswap32((value));                       \
    _ptr_out = template_asn1_integer_impl(_ptr_out, (tag), (tweak_msb), \
                                          (uint8_t *)&_value, 4);       \
  }

uint8_t *template_asn1_integer_impl(uint8_t *out, uint8_t tag, bool tweak_msb,
                                    const uint8_t *bytes_be, size_t size);

/**
 * Memo a location to be patch with the actual output size.
 *
 * The function will saved the address (last output byte + offset) for
 * patching later, and it should be paired with a `template_patch_size_*`.
 *
 * @param offset Number of bytes after the last output byte.
 */
#define template_memo_size(offset) uint8_t *_ptr_tag = _ptr_out + (offset);

void template_patch_size_be_impl(uint16_t *_ptr_tag, uint8_t *_ptr_out);

/**
 * Add the actual output size after the memo to the patch location.
 *
 * The function will perform addition as LE u16 (i.e. mod 65536).
 */
#define template_patch_size_le() \
  { *(uint16_t *)_ptr_tag += (uint16_t)(_ptr_out - _ptr_tag); }

/**
 * Add the actual output size after the memo to the patch location.
 *
 * The function will perform addition as BE u16 (i.e. mod 65536).
 */
#define template_patch_size_be() \
  { template_patch_size_be_impl((uint16_t *)_ptr_tag, _ptr_out); }

#ifdef __cplusplus
}  // extern "C"
#endif  // __cplusplus

#endif  // OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_CERT_TEMPLATE_H_
