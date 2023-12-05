// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/silicon_creator/lib/cert/asn1.h"

#include <limits.h>

rom_error_t asn1_start(asn1_state_t *new_state, uint8_t *buffer, size_t size) {
  // Make sure that the buffer is not too large to prevent overflows.
  if (new_state == NULL || buffer == NULL || size > PTRDIFF_MAX) {
    return kErrorAsn1InvalidArgument;
  }
  new_state->buffer = buffer;
  new_state->size = size;
  new_state->offset = 0;
  return kErrorOk;
}

rom_error_t asn1_finish(asn1_state_t *state, size_t *out_size) {
  *out_size = state->offset;
  state->buffer = 0;
  state->size = 0;
  state->offset = 0;
  return kErrorOk;
}

rom_error_t asn1_push_byte(asn1_state_t *state, uint8_t byte) {
  return asn1_push_bytes(state, &byte, 1);
}

rom_error_t asn1_push_bytes(asn1_state_t *state, const uint8_t *bytes,
                            size_t size) {
  // Make sure that the addition will not overflow
  if (size > PTRDIFF_MAX) {
    return kErrorAsn1InvalidArgument;
  }
  if (state->offset + size > state->size) {
    return kErrorAsn1BufferExhausted;
  }
  memcpy(state->buffer + state->offset, bytes, size);
  state->offset += size;
  return kErrorOk;
}

rom_error_t asn1_start_tag(asn1_state_t *state, asn1_tag_t *new_tag,
                           uint8_t id) {
  new_tag->state = state;
  RETURN_IF_ERROR(asn1_push_byte(state, id));
  new_tag->len_offset = state->offset;
  // We do not yet known how many bytes we need to encode the length. For now
  // reserve three bytes so we can use the 16-bit encoding. This is then fixed
  // in asn1_finish_tag.

  // Three bytes: one to hold the number of octets to use
  // and two to store the length.
  RETURN_IF_ERROR(asn1_push_bytes(state, (uint8_t[]){0x82, 0, 0}, 3));
  new_tag->len_size = 3;
  return kErrorOk;
}

rom_error_t asn1_finish_tag(asn1_tag_t *tag) {
  // Robustness check against accidently reusing a finished tag.
  if (tag->state == NULL) {
    return kErrorAsn1Internal;
  }
  // Sanity check: asn1_start_tag should have output three bytes.
  if (tag->len_size != 3) {
    return kErrorAsn1Internal;
  }
  // Compute actually used length.
  size_t length = tag->state->offset - tag->len_offset - tag->len_size;
  // Fixup the length bytes and compute the size of the minimal encoding.
  size_t final_len_size;
  if (length <= 0x7f) {
    // We only need one byte to hold the length.
    tag->state->buffer[tag->len_offset] = (uint8_t)length;
    final_len_size = 1;
  } else if (length <= 0xff) {
    // We need two bytes to hold the length.
    tag->state->buffer[tag->len_offset + 0] = 0x81;
    tag->state->buffer[tag->len_offset + 1] = (uint8_t)length;
    final_len_size = 2;
  } else if (length <= 0xffff) {
    // We need three bytes to hold the length.
    tag->state->buffer[tag->len_offset + 0] = 0x82;
    tag->state->buffer[tag->len_offset + 1] = (uint8_t)(length >> 8);
    tag->state->buffer[tag->len_offset + 2] = (uint8_t)(length & 0xff);
    final_len_size = 3;
  } else {
    // Length too large.
    return kErrorAsn1Internal;
  }
  // If the final length uses less bytes than we initially allocated, we
  // need to shift all the tag data forward.
  for (size_t i = 0; i < length; i++) {
    tag->state->buffer[tag->len_offset + final_len_size + i] =
        tag->state->buffer[tag->len_offset + tag->len_size + i];
  }
  // Fix up state offset.
  tag->state->offset -= tag->len_size - final_len_size;
  // Hardening: clear out the tag structure to prevent accidental reuse.
  tag->state = NULL;
  tag->len_offset = 0;
  tag->len_size = 0;
  return kErrorOk;
}

rom_error_t asn1_push_bool(asn1_state_t *state, bool value) {
  asn1_tag_t tag;
  RETURN_IF_ERROR(asn1_start_tag(state, &tag, kAsn1TagNumberBoolean));
  RETURN_IF_ERROR(asn1_push_byte(state, value ? 0xff : 0));
  return asn1_finish_tag(&tag);
}

rom_error_t asn1_push_int32(asn1_state_t *state, uint8_t tag, int32_t value) {
  uint32_t u_value = (uint32_t)value;
  uint8_t bigint[4] = {
      u_value >> 24,
      (u_value >> 16) & 0xff,
      (u_value >> 8) & 0xff,
      u_value & 0xff,
  };
  return asn1_push_integer(state, tag, true, bigint, sizeof(bigint));
}

rom_error_t asn1_push_uint32(asn1_state_t *state, uint8_t tag, uint32_t value) {
  uint8_t bigint[4] = {
      value >> 24,
      (value >> 16) & 0xff,
      (value >> 8) & 0xff,
      value & 0xff,
  };
  return asn1_push_integer(state, tag, false, bigint, sizeof(bigint));
}

rom_error_t asn1_push_integer(asn1_state_t *state, uint8_t tag, bool is_signed,
                              const uint8_t *bytes_be, size_t size) {
  if (size == 0) {
    return kErrorAsn1InvalidArgument;
  }
  asn1_tag_t tag_st;
  RETURN_IF_ERROR(asn1_start_tag(state, &tag_st, tag));
  // Compute smallest possible encoding: ASN1 forbids that the first 9 bits (ie
  // first octet) and MSB of the second octet are either all ones or all zeroes.

  // First get rid of unnecessary zeroes.
  while (size >= 2 && bytes_be[0] == 0 && (bytes_be[1] >> 7) == 0) {
    bytes_be++;
    size -= 1;
  }

  if (is_signed) {
    // Integers in ASN.1 are always signed and represented in two's complement.
    // So for unsigned numbers that has MSB set, add a 0x00 padding.
    while (size >= 2 && bytes_be[0] == 0xff && (bytes_be[1] >> 7) == 1) {
      bytes_be++;
      size -= 1;
    }
  } else {
    // For unsigned numbers, add a 0x00 padding if the first octet has MSB set.
    if ((bytes_be[0] >> 7) == 1) {
      RETURN_IF_ERROR(asn1_push_byte(state, 0));
    }
  }
  RETURN_IF_ERROR(asn1_push_bytes(state, bytes_be, size));
  return asn1_finish_tag(&tag_st);
}

rom_error_t asn1_push_oid_raw(asn1_state_t *state, const uint8_t *bytes,
                              size_t size) {
  asn1_tag_t tag;
  RETURN_IF_ERROR(asn1_start_tag(state, &tag, kAsn1TagNumberOid));
  RETURN_IF_ERROR(asn1_push_bytes(state, bytes, size));
  return asn1_finish_tag(&tag);
}

rom_error_t asn1_push_string(asn1_state_t *state, uint8_t id, const char *str,
                             size_t max_len) {
  asn1_tag_t tag;
  RETURN_IF_ERROR(asn1_start_tag(state, &tag, id));
  while (max_len > 0 && str[0] != 0) {
    RETURN_IF_ERROR(asn1_push_byte(state, (uint8_t)str[0]));
    str++;
    max_len--;
  }
  return asn1_finish_tag(&tag);
}

static const char kLowercaseHexChars[16] = {'0', '1', '2', '3', '4', '5',
                                            '6', '7', '8', '9', 'a', 'b',
                                            'c', 'd', 'e', 'f'};

rom_error_t asn1_push_hexstring(asn1_state_t *state, uint8_t id,
                                const uint8_t *bytes, size_t size) {
  asn1_tag_t tag;
  RETURN_IF_ERROR(asn1_start_tag(state, &tag, id));
  while (size > 0) {
    RETURN_IF_ERROR(
        asn1_push_byte(state, (uint8_t)kLowercaseHexChars[bytes[0] >> 4]));
    RETURN_IF_ERROR(
        asn1_push_byte(state, (uint8_t)kLowercaseHexChars[bytes[0] & 0xf]));
    bytes++;
    size--;
  }
  return asn1_finish_tag(&tag);
}
