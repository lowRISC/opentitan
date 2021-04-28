// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/dif/dif_kmac.h"

#include <assert.h>

#include "sw/device/lib/base/memory.h"

// TODO: implement!

dif_kmac_result_t dif_kmac_customization_string_init(
    const char *data, size_t len, dif_kmac_customization_string_t *out) {
  if ((data == NULL && len != 0) || out == NULL) {
    return kDifKmacBadArg;
  }

  if (len > kDifKmacMaxCustomizationStringLen) {
    return kDifKmacBadArg;
  }

  static_assert(kDifKmacMaxCustomizationStringLen <= UINT16_MAX / 8,
                "length requires more than 3 bytes to left encode");
  static_assert(ARRAYSIZE(out->buffer) >= kDifKmacMaxCustomizationStringLen + 3,
                "buffer is not large enough");

  // Left encode length in bits.
  uint16_t bits = ((uint16_t)len) * 8;
  char *buffer = out->buffer;
  if (bits <= UINT8_MAX) {
    *buffer++ = 1;
    *buffer++ = (char)bits;
  } else {
    *buffer++ = 2;
    // Most significant byte is first (i.e. big-endian).
    *buffer++ = (char)(bits >> 8);
    *buffer++ = (char)bits;
  }

  memcpy(buffer, data, len);

  return kDifKmacOk;
}

dif_kmac_result_t dif_kmac_function_name_init(const char *data, size_t len,
                                              dif_kmac_function_name_t *out) {
  if ((data == NULL && len != 0) || out == NULL) {
    return kDifKmacBadArg;
  }

  if (len > kDifKmacMaxFunctionNameLen) {
    return kDifKmacBadArg;
  }

  static_assert(kDifKmacMaxFunctionNameLen <= UINT8_MAX / 8,
                "length requires more than 2 bytes to left encode");
  static_assert(ARRAYSIZE(out->buffer) >= kDifKmacMaxFunctionNameLen + 2,
                "buffer is not large enough");

  // Left encode length in bits.
  out->buffer[0] = 1;
  out->buffer[1] = (char)(len * 8);

  memcpy(&out->buffer[2], data, len);

  return kDifKmacOk;
}
