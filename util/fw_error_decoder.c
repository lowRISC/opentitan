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
const static char *prog_name;

static void usage(int return_code) {
  FILE *output_file;

  if (return_code) {
    output_file = stderr;
  } else {
    output_file = stdout;
  }

  fprintf(output_file,
          "Usage:\n"
          "   %s [<hex fw error code> ..]\n",
          prog_name);
  exit(return_code);
}

int main(int argc, char **argv) {
  size_t i = 1;

  prog_name = strrchr(argv[0], '/');
  if (!prog_name++) {
    prog_name = argv[0];
  }

  if (argc == 1) {
    usage(0);
  }

  while (i < argc) {
    char *end;
    const char *code = argv[i++];
    long error_value = strtol(code, &end, 16);

    if (*end) {
      fprintf(stderr, "'%s' is not a hex value\n", code);
      usage(1);
    }

    printf("%08lx: ", error_value);

    const error_descriptor_t *edesc = error_table;

    while (edesc->value) {
      if (edesc->value == error_value) {
        printf("%s\n", edesc->text);
        break;
      }
      edesc++;
    }

    if (edesc->value) {
      continue;
    }

    unsigned char mod_high = (error_value >> 16) & 0xff;
    unsigned char mod_low = (error_value >> 8) & 0xff;

    if (((mod_high == 'R') && (mod_low == 'I')) ||
        ((mod_high == 'I') && (mod_low == 'R'))) {
      // This is an interrupt/exception error, retrieve the encoded mcause.
      uint32_t mcause =
          (error_value & (1 << 31)) | ((error_value >> 24) & 0x7f);

      if (mod_high == 'R') {
        printf("ROM_EXT ");
      }

      printf("interrupt/exception, mcause 0x%08x, status 0x%02lx\n", mcause,
             error_value & 0xff);
      continue;
    }

    printf("unknown error code\n");
  }
}
