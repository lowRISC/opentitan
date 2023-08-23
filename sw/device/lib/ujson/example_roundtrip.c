// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "sw/device/lib/base/status.h"
#include "sw/device/lib/ujson/example.h"
#include "sw/device/silicon_creator/lib/crc32.h"

status_t stdio_getc(void *context) {
  int ch = fgetc(stdin);
  return ch == EOF ? RESOURCE_EXHAUSTED() : OK_STATUS(ch);
}

status_t stdio_putbuf(void *context, const char *buf, size_t len) {
  fwrite(buf, 1, len, stdout);
  return OK_STATUS();
}

status_t check_crc32(ujson_t *uj) {
  uint32_t expected = ujson_crc32_finish(uj);
  uint32_t actual;
  scanf("%x", &actual);

  if (expected != actual) {
    fprintf(stderr, "CRC32 Error: expected = %x, actual = %x\n", expected,
            actual);
    return DATA_LOSS();
  };
  return OK_STATUS();
}

status_t roundtrip(const char *name) {
  ujson_t uj = ujson_init(NULL, stdio_getc, stdio_putbuf);
  if (!strcmp(name, "foo")) {
    foo x = {0};
    TRY(ujson_deserialize_foo(&uj, &x));
    TRY(check_crc32(&uj));
    ujson_crc32_reset(&uj);
    TRY(ujson_serialize_foo(&uj, &x));
    printf("\n%x", ujson_crc32_finish(&uj));
  } else if (!strcmp(name, "rect")) {
    rect x = {0};
    TRY(ujson_deserialize_rect(&uj, &x));
    TRY(check_crc32(&uj));
    ujson_crc32_reset(&uj);
    TRY(ujson_serialize_rect(&uj, &x));
    printf("\n%x", ujson_crc32_finish(&uj));
  } else if (!strcmp(name, "matrix")) {
    matrix x = {0};
    TRY(ujson_deserialize_matrix(&uj, &x));
    TRY(check_crc32(&uj));
    ujson_crc32_reset(&uj);
    TRY(ujson_serialize_matrix(&uj, &x));
    printf("\n%x", ujson_crc32_finish(&uj));
  } else if (!strcmp(name, "direction")) {
    direction x = {0};
    TRY(ujson_deserialize_direction(&uj, &x));
    TRY(check_crc32(&uj));
    ujson_crc32_reset(&uj);
    TRY(ujson_serialize_direction(&uj, &x));
    printf("\n%x", ujson_crc32_finish(&uj));
  } else if (!strcmp(name, "fuzzy_bool")) {
    fuzzy_bool x = {0};
    TRY(ujson_deserialize_fuzzy_bool(&uj, &x));
    TRY(check_crc32(&uj));
    ujson_crc32_reset(&uj);
    TRY(ujson_serialize_fuzzy_bool(&uj, &x));
    printf("\n%x", ujson_crc32_finish(&uj));
  } else if (!strcmp(name, "fuzzy_bool_no_crc")) {
    fuzzy_bool x = {0};
    TRY(ujson_deserialize_fuzzy_bool(&uj, &x));
    TRY(ujson_serialize_fuzzy_bool(&uj, &x));
  } else if (!strcmp(name, "misc")) {
    misc_t x = {0};
    TRY(ujson_deserialize_misc_t(&uj, &x));
    TRY(check_crc32(&uj));
    ujson_crc32_reset(&uj);
    TRY(ujson_serialize_misc_t(&uj, &x));
    printf("\n%x", ujson_crc32_finish(&uj));
  } else {
    return INVALID_ARGUMENT();
  }
  return OK_STATUS();
}

int main(int argc, char *argv[]) {
  if (argc < 2) {
    fprintf(stderr, "%s [struct-name]", argv[0]);
    return EXIT_FAILURE;
  }
  status_t s = roundtrip(argv[1]);

  return status_ok(s) ? EXIT_SUCCESS : EXIT_FAILURE;
}
