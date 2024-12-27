// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "sw/device/silicon_creator/lib/error.h"

typedef struct {
  const char *text;
  int value;
} error_descriptor_t;

#define ERROR_TABLE_ENTRY(name, value) \
  { #name, value }

// Add an empty element in the end to make it easier to stop iterating over the
// table.
const static error_descriptor_t error_table[] = {
    DEFINE_ERRORS(ERROR_TABLE_ENTRY){}};

size_t bfv_decoder(uint32_t bfv, uint8_t *buf, size_t buf_size) {
  char *str = (char *)buf;

  const error_descriptor_t *edesc = error_table;

  while (edesc->value) {
    if (edesc->value == bfv) {
      snprintf(str, buf_size, "%s", edesc->text);
      break;
    }
    edesc++;
  }
  if (!edesc->value) {
    // This was not an encoded BFV, must have been an exception.
    unsigned char mod_high = (bfv >> 16) & 0xff;
    unsigned char mod_low = (bfv >> 8) & 0xff;

    if (((mod_high == 'R') && (mod_low == 'I')) ||
        ((mod_high == 'I') && (mod_low == 'R'))) {
      // This is an interrupt/exception error, retrieve the encoded mcause.
      uint32_t mcause = (bfv & (1 << 31)) | ((bfv >> 24) & 0x7f);
      const char *prefix = "";

      if (mod_high == 'R') {
        prefix = "ROM_EXT ";
      }

      snprintf(str, buf_size,
               "%sinterrupt/exception, mcause 0x%08x, status 0x%02x", prefix,
               mcause, bfv & 0xff);
    } else {
      snprintf(str, buf_size, "unknown error code");
    }
  }
  return strlen(str);
}
