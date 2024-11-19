// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/silicon_creator/lib/cert/asn1.h"

#include <limits.h>

/**
 * Return if the given asn1 state has an active error.
 *
 * @param state Pointer to a user-allocated `asn1_state_t` state.
 */
#define RETURN_IF_ASN1_ERROR(state)   \
  do {                                \
    if ((state)->error != kErrorOk) { \
      return;                         \
    }                                 \
  } while (false);

/**
 * Set the active error in asn1 state to `error_code` and return.
 *
 * @param state Pointer to a user-allocated `asn1_state_t` state.
 */
#define RAISE_ASN1_ERROR(state, error_code) \
  do {                                      \
    (state)->error = (error_code);          \
    return;                                 \
  } while (false);

void asn1_clear_error(asn1_state_t *state) { state->error = kErrorOk; }

rom_error_t asn1_start(asn1_state_t *new_state, uint8_t *buffer, size_t size) {
  // Make sure that the buffer is not too large to prevent overflows.
  if (new_state == NULL || buffer == NULL || size > PTRDIFF_MAX) {
    return kErrorAsn1StartInvalidArgument;
  }
  new_state->buffer = buffer;
  new_state->size = size;
  new_state->offset = 0;
  asn1_clear_error(new_state);
  return kErrorOk;
}

rom_error_t asn1_finish(asn1_state_t *state, size_t *out_size) {
  rom_error_t result = state->error;
  *out_size = state->offset;
  state->buffer = NULL;
  state->size = 0;
  state->offset = 0;
  asn1_clear_error(state);
  return result;
}

void asn1_push_byte(asn1_state_t *state, uint8_t byte) {
  asn1_push_bytes(state, &byte, 1);
}

void asn1_push_bytes(asn1_state_t *state, const uint8_t *bytes, size_t size) {
  RETURN_IF_ASN1_ERROR(state);

  // Make sure that the addition will not overflow
  if (size > PTRDIFF_MAX || state->offset > PTRDIFF_MAX) {
    RAISE_ASN1_ERROR(state, kErrorAsn1PushBytesInvalidArgument);
  }
  if (state->offset + size > state->size) {
    RAISE_ASN1_ERROR(state, kErrorAsn1BufferExhausted);
  }
  memcpy(state->buffer + state->offset, bytes, size);
  state->offset += size;
}

void asn1_start_tag(asn1_state_t *state, asn1_tag_t *new_tag, uint8_t id) {
  new_tag->state = NULL;
  RETURN_IF_ASN1_ERROR(state);

  new_tag->state = state;
  asn1_push_byte(state, id);
  RETURN_IF_ASN1_ERROR(state);
  new_tag->len_offset = state->offset;
  // We do not yet known how many bytes we need to encode the length. For now
  // reserve one byte which is the minimum. This is then fixed in
  // asn1_finish_tag by moving the data if necessary.

  asn1_push_byte(state, 0);
  RETURN_IF_ASN1_ERROR(state);
  new_tag->len_size = 1;
}

void asn1_finish_tag(asn1_tag_t *tag) {
  if (tag->state == NULL)
    return;
  RETURN_IF_ASN1_ERROR(tag->state);
  // Sanity check: asn1_start_tag should have output one byte.
  if (tag->len_size != 1) {
    RAISE_ASN1_ERROR(tag->state, kErrorAsn1Internal);
  }
  // Compute actually used length.
  size_t length = tag->state->offset - tag->len_offset - tag->len_size;
  // Compute the size of the minimal encoding.
  size_t final_len_size;
  if (length <= 0x7f) {
    // We only need one byte to hold the length.
    final_len_size = 1;
  } else if (length <= 0xff) {
    // We need two bytes to hold the length: we need to move the data before
    // we can write the second byte.
    final_len_size = 2;
  } else if (length <= 0xffff) {
    // We need three bytes to hold the length: we need to move the data before
    // we can write the second and third bytes.
    final_len_size = 3;
  } else {
    // Length too large.
    RAISE_ASN1_ERROR(tag->state, kErrorAsn1Internal);
  }
  // If the final length uses more bytes than we initially allocated, we
  // need to shift all the tag data backwards.
  if (tag->len_size != final_len_size) {
    // Make sure that the data actually fits into the buffer.
    size_t new_buffer_size =
        tag->state->offset + final_len_size - tag->len_size;
    if (new_buffer_size > tag->state->size) {
      RAISE_ASN1_ERROR(tag->state, kErrorAsn1BufferExhausted);
    }
    // Copy backwards.
    for (size_t i = 0; i < length; i++) {
      tag->state->buffer[tag->len_offset + final_len_size + length - 1 - i] =
          tag->state->buffer[tag->len_offset + tag->len_size + length - 1 - i];
    }
  }
  // Write the length in the buffer.
  if (length <= 0x7f) {
    tag->state->buffer[tag->len_offset] = (uint8_t)length;
  } else if (length <= 0xff) {
    tag->state->buffer[tag->len_offset + 0] = 0x81;
    tag->state->buffer[tag->len_offset + 1] = (uint8_t)length;
  } else if (length <= 0xffff) {
    tag->state->buffer[tag->len_offset + 0] = 0x82;
    tag->state->buffer[tag->len_offset + 1] = (uint8_t)(length >> 8);
    tag->state->buffer[tag->len_offset + 2] = (uint8_t)(length & 0xff);
  } else {
    // Length too large.
    RAISE_ASN1_ERROR(tag->state, kErrorAsn1Internal);
  }
  // Fix up state offset.
  tag->state->offset += final_len_size - tag->len_size;
  // Hardening: clear out the tag structure to prevent accidental reuse.
  tag->state = NULL;
  tag->len_offset = 0;
  tag->len_size = 0;
}

void asn1_push_bool(asn1_state_t *state, uint8_t tag, bool value) {
  asn1_tag_t tag_st;
  asn1_start_tag(state, &tag_st, tag);
  asn1_push_byte(state, value ? 0xff : 0);
  asn1_finish_tag(&tag_st);
}

void asn1_push_int32(asn1_state_t *state, uint8_t tag, int32_t value) {
  uint32_t u_value = (uint32_t)value;
  uint8_t bigint[4] = {
      u_value >> 24,
      (u_value >> 16) & 0xff,
      (u_value >> 8) & 0xff,
      u_value & 0xff,
  };
  asn1_push_integer(state, tag, true, bigint, sizeof(bigint));
}

void asn1_push_uint32(asn1_state_t *state, uint8_t tag, uint32_t value) {
  uint8_t bigint[4] = {
      value >> 24,
      (value >> 16) & 0xff,
      (value >> 8) & 0xff,
      value & 0xff,
  };
  asn1_push_integer(state, tag, false, bigint, sizeof(bigint));
}

void asn1_push_integer(asn1_state_t *state, uint8_t tag, bool is_signed,
                       const uint8_t *bytes_be, size_t size) {
  RETURN_IF_ASN1_ERROR(state);
  if (size == 0 || (bytes_be == NULL && size > 0)) {
    RAISE_ASN1_ERROR(state, kErrorAsn1PushIntegerInvalidArgument);
  }
  asn1_tag_t tag_st;
  asn1_start_tag(state, &tag_st, tag);
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
      asn1_push_byte(state, 0);
    }
  }
  asn1_push_bytes(state, bytes_be, size);
  asn1_finish_tag(&tag_st);
}

void asn1_push_integer_pad(asn1_state_t *state, bool is_signed,
                           const uint8_t *bytes_be, size_t size,
                           size_t padded_size) {
  RETURN_IF_ASN1_ERROR(state);
  if (size == 0 || size > padded_size) {
    RAISE_ASN1_ERROR(state, kErrorAsn1PushIntegerPadInvalidArgument);
  }
  // Determine the padding byte.
  uint8_t padding = 0;
  if (is_signed && (bytes_be[0] >> 7) == 1) {
    padding = 0xff;
  }
  // Output padding.
  while (padded_size-- > size) {
    asn1_push_byte(state, padding);
  }
  asn1_push_bytes(state, bytes_be, size);
}

void asn1_push_oid_raw(asn1_state_t *state, const uint8_t *bytes, size_t size) {
  asn1_tag_t tag;
  asn1_start_tag(state, &tag, kAsn1TagNumberOid);
  asn1_push_bytes(state, bytes, size);
  asn1_finish_tag(&tag);
}

void asn1_push_string(asn1_state_t *state, uint8_t id, const char *str,
                      size_t max_len) {
  asn1_tag_t tag;
  asn1_start_tag(state, &tag, id);
  while (max_len > 0 && str[0] != 0) {
    asn1_push_byte(state, (uint8_t)str[0]);
    str++;
    max_len--;
  }
  asn1_finish_tag(&tag);
}

static const char kLowercaseHexChars[16] = {'0', '1', '2', '3', '4', '5',
                                            '6', '7', '8', '9', 'a', 'b',
                                            'c', 'd', 'e', 'f'};

void asn1_push_hexstring(asn1_state_t *state, uint8_t id, const uint8_t *bytes,
                         size_t size) {
  asn1_tag_t tag;
  asn1_start_tag(state, &tag, id);
  while (size > 0) {
    asn1_push_byte(state, (uint8_t)kLowercaseHexChars[bytes[0] >> 4]);
    asn1_push_byte(state, (uint8_t)kLowercaseHexChars[bytes[0] & 0xf]);
    bytes++;
    size--;
  }
  asn1_finish_tag(&tag);
}

void asn1_start_bitstring(asn1_state_t *state,
                          asn1_bitstring_t *out_bitstring) {
  out_bitstring->state = NULL;
  RETURN_IF_ASN1_ERROR(state);
  out_bitstring->state = state;
  out_bitstring->unused_bits_offset = state->offset;
  out_bitstring->used_bits = 0;
  out_bitstring->current_byte = 0;
  // Push a single byte that will hold the unused bit count (it will be updated
  // in asn1_finish_bitstring.
  asn1_push_byte(state, 0);
}

void asn1_bitstring_push_bit(asn1_bitstring_t *bitstring, bool bit) {
  if (bitstring->state == NULL)
    return;
  RETURN_IF_ASN1_ERROR(bitstring->state);
  // Update the current byte: bits are added from MSB to LSB.
  if (bit) {
    bitstring->current_byte |= 1 << (7 - bitstring->used_bits);
  }
  // If this makes a full byte, push it and reset.
  bitstring->used_bits++;
  if (bitstring->used_bits == 8) {
    asn1_push_byte(bitstring->state, bitstring->current_byte);
    bitstring->current_byte = 0;
    bitstring->used_bits = 0;
  }
}

void asn1_finish_bitstring(asn1_bitstring_t *bitstring) {
  if (bitstring->state == NULL)
    return;
  RETURN_IF_ASN1_ERROR(bitstring->state);
  if (bitstring->used_bits >= 8) {
    asn1_state_t *state = bitstring->state;
    bitstring->state = NULL;
    RAISE_ASN1_ERROR(state, kErrorAsn1FinishBitstringInvalidArgument);
  }
  // If the last byte contains some bits, we need to push it and update
  // the number of unused bits. If the string length was a multiple of 8
  // (ie used_bits = 0) then there are 0 unused bits which is the value pushed
  // in asn1_start_bitstring so we do not need to update it.
  if (bitstring->used_bits != 0) {
    asn1_push_byte(bitstring->state, bitstring->current_byte);
    // Update the "unused bits value"
    bitstring->state->buffer[bitstring->unused_bits_offset] =
        8 - (uint8_t)bitstring->used_bits;
  }
  // Hardening: clear out the tag structure to prevent accidental reuse.
  bitstring->state = NULL;
}
