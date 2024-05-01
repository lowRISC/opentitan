// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/silicon_creator/manuf/skus/earlgrey_a0/sival_bringup/util.h"

#include "sw/device/lib/runtime/log.h"
#include "sw/device/silicon_creator/lib/base/boot_measurements.h"

uint32_t round_up_to(uint32_t input, uint32_t align_bits) {
  uint32_t mask = (1 << align_bits) - 1;
  return (input + mask) & ~mask;
}

uint32_t size_to_words(uint32_t bytes) {
  return round_up_to(bytes, 2) / sizeof(uint32_t);
}

uint32_t get_cert_size(const uint8_t *header) {
  if (header[0] != 0x30 || header[1] != 0x82) {
    return 0;
  }
  return (((uint32_t)header[2]) << 8) + header[3] + 4 /* size of the header */;
}

void log_self_hash(void) {
  // clang-format off
  LOG_INFO("Personalization Firmware Hash: 0x%08x%08x%08x%08x%08x%08x%08x%08x",
           boot_measurements.rom_ext.data[7],
           boot_measurements.rom_ext.data[6],
           boot_measurements.rom_ext.data[5],
           boot_measurements.rom_ext.data[4],
           boot_measurements.rom_ext.data[3],
           boot_measurements.rom_ext.data[2],
           boot_measurements.rom_ext.data[1],
           boot_measurements.rom_ext.data[0]);
  // clang-format on
}
