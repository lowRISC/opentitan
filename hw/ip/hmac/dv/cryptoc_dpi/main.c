// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Standalone command line utility to calculate the SHA2-256/384/512 of an
// input file, which may be compared directly against the output of the
// system utilities 'sha256sum', 'sha384sum' and 'sha512sum' for
// verification.
//
// Build with eg.
// gcc -o sha256 -Wall -Werror main.c sha256.c sha384.c sha512.c
// gcc -o sha384 -Wall -Werror main.c sha256.c sha384.c sha512.c
// gcc -o sha512 -Wall -Werror main.c sha256.c sha384.c sha512.c
//
// The utility simply consults the final character of its executable name
// to determine the algorithm to apply.

#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "sha256.h"
#ifdef SHA512_SUPPORT
#include "sha384.h"
#include "sha512.h"
#endif

typedef enum { Opcode256, Opcode384, Opcode512 } opcode_t;

int main(int argc, char *argv[]) {
  if (argc < 2) {
    fprintf(stderr, "Syntax: %s <input file>\n", argv[0]);
    return 1;
  }

  const char *infile = argv[1];
  FILE *out = stdout;

  const char *opc = argv[0] + strlen(argv[0]) - 1;
  opcode_t opcode;
  switch (*opc) {
    case '2':
      opcode = Opcode512;
      break;
    case '4':
      opcode = Opcode384;
      break;
    default:
      opcode = Opcode256;
      break;
  }

  FILE *in = fopen(infile, "rb");
  if (!in) {
    fprintf(stderr, "Cannot open input file '%s'\n", infile);
    return 2;
  }
  fseek(in, 0, SEEK_END);
  long file_len = ftell(in);
  rewind(in);
  uint8_t *buf = malloc(file_len);
  if (!buf) {
    fprintf(stderr, "Not enough memory to load '%s' (%lu bytes required)\n",
            infile, file_len);
    fclose(in);
    return 3;
  }
  fread(buf, file_len, 1, in);
  fclose(in);

  uint8_t digest[64];
  unsigned digest_size = 64;
  switch (opcode) {
#ifdef SHA512_SUPPORT
    case Opcode512:
      SHA512_hash(buf, file_len, digest);
      break;
    case Opcode384:
      SHA384_hash(buf, file_len, digest);
      digest_size = 48;
      break;
#endif
    default:
      SHA256_hash(buf, file_len, digest);
      digest_size = 32;
      break;
  }

  free(buf);

  for (unsigned idx = 0u; idx < digest_size; ++idx) {
    static const char lower_xdigits[] = "0123456789abcdef";

    fputc(lower_xdigits[digest[idx] >> 4], out);
    fputc(lower_xdigits[digest[idx] & 0xf], out);
  }
  fputs("  ", out);
  puts(infile);

  return 0;
}
