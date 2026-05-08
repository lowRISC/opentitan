// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/base/status.h"

#include <stdbool.h>
#include <stdint.h>

#include "sw/device/lib/base/bitfield.h"

const uint32_t MODULE_ID = 0;

static const char *basename(const char *file, size_t *basename_len) {
  const char *f = file;
  // Go to the end of the string.
  while (*f)
    ++f;
  // Back up to the start of the last filename path component.
  *basename_len = 0;
  while (f > file && f[-1] != '/' && f[-1] != '\\') {
    ++(*basename_len);
    --f;
  }
  return f;
}

status_t status_from_rom_error(uint32_t val) {
  uint32_t code =
      val == kErrorOk ? 0 : bitfield_field32_read(val, ROM_ERROR_FIELD_STATUS);
  int32_t arg = (int32_t)bitfield_field32_read(val, ROM_ERROR_FIELD_ERROR);
  uint32_t mod = bitfield_field32_read(val, ROM_ERROR_FIELD_MODULE);
  uint32_t module = (mod & 0x1F) << 16 | (mod & 0x1F00) << (21 - 8);
  /* We know that the module ID extracted from the rom_error_t is not undefined
   * so there is no point in passing a filename to status_created. */
  return status_create((absl_status_t)code, module, "unk",
                       code == kOk ? kErrorOk : arg);
}

status_t status_create(absl_status_t code, uint32_t module_id, const char *file,
                       int32_t arg) {
  if (code == kOk) {
    if (arg >= 0) {
      return (status_t){.value = arg};
    } else {
      // If you find yourself here, then someone returned a OK_STATUS
      // a negative value.
      arg = __LINE__;
    }
  }
  /**
   * Our status(error) codes are arranged as a packed bitfield:
   *
   * 32  31      26      21      16             5       0
   *  +---+-------+-------+-------+-------------+-------+
   *  |   |   15 bit              | 11 bit      | 5 bit |
   *  | s |   Module Identifier   | Line Number | code  |
   *  +---+-------+-------+-------+-------------+-------+
   *
   * The sign bit is set on all not-Ok statuses, thus proviging a covenient
   * overloaded return value from functions that may return an error.
   */
  if (module_id == 0) {
    // First three characters of the filename.
    size_t basename_len = 0;
    const char *f = basename(file, &basename_len);
    module_id = basename_len >= 3 ? MAKE_MODULE_ID(f[0], f[1], f[2])
                                  : MAKE_MODULE_ID('u', 'n', 'd');
  }
  // The module ID currently encodes one ASCII in each 8-bit field. To make
  // the three ASCII fit in 15 bits, we convert to 5-bit ASCII characters.
  module_id = status_encode_module_id(module_id);
  // At this point, the module_id is already packed into the correct bitfield.
  return (status_t){
      .value = (int32_t)(bitfield_field32_write(0, STATUS_FIELD_MODULE_ID,
                                                module_id) |
                         bitfield_bit32_write(0, STATUS_BIT_ERROR, true) |
                         bitfield_field32_write(0, STATUS_FIELD_CODE, code) |
                         bitfield_field32_write(0, STATUS_FIELD_ARG,
                                                (uint32_t)arg))};
}

const char *status_codes[] = {
    "Ok",
    "Cancelled",
    "Unknown",
    "InvalidArgument",
    "DeadlineExceeded",
    "NotFound",
    "AlreadyExists",
    "PermissionDenied",
    "ResourceExhausted",
    "FailedPrecondition",
    "Aborted",
    "OutOfRange",
    "Unimplemented",
    "Internal",
    "Unavailable",
    "DataLoss",
    "Unauthenticated",

    "Undefined17",
    "Undefined18",
    "Undefined19",
    "Undefined20",
    "Undefined21",
    "Undefined22",
    "Undefined23",
    "Undefined24",
    "Undefined25",
    "Undefined26",
    "Undefined27",
    "Undefined28",
    "Undefined29",
    "Undefined30",
    "Undefined31",

    // A "ErrorError" means the error bit is set but the err field is kOk.
    "ErrorError",
};

bool status_extract(status_t s, const char **code, int32_t *arg, char *mod_id) {
  size_t err = (size_t)status_err(s);
  if (s.value < 0 && err == 0) {
    err = sizeof(status_codes) / sizeof(status_codes[0]) - 1;
  }
  *code = status_codes[err];
  if (err) {
    *arg = (int32_t)bitfield_field32_read((uint32_t)s.value, STATUS_FIELD_ARG);
    uint32_t module_id =
        bitfield_field32_read((uint32_t)s.value, STATUS_FIELD_MODULE_ID);
    *mod_id++ = '@' + ((module_id >> 0) & 0x1F);
    *mod_id++ = '@' + ((module_id >> 5) & 0x1F);
    *mod_id++ = '@' + ((module_id >> 10) & 0x1F);
    return true;
  } else {
    *arg = s.value;
    return false;
  }
}

extern bool status_ok(status_t s);
extern absl_status_t status_err(status_t s);

// This is a weak implementation that does nothing. This way it can easily be
// overidden and does not require every user of status to manually add a
// dependency.
OT_WEAK
void status_report(status_t value) { (void)value; }
