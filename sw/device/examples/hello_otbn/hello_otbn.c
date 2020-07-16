// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/arch/device.h"
#include "sw/device/lib/base/log.h"
#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/dif/dif_otbn.h"
#include "sw/device/lib/runtime/hart.h"
#include "sw/device/lib/testing/test_status.h"
#include "sw/device/lib/uart.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

static dif_otbn_t otbn;

void run(size_t otbn_imem_size, const uint32_t *otbn_imem,
         size_t otbn_dmem_size, const uint32_t *otbn_dmem,
         uint32_t *otbn_dmem_readback) {
  static uint32_t otbn_imem_readback[1024];

  LOG_INFO("Writing OTBN IMEM");
  if (dif_otbn_imem_write(&otbn, 0, otbn_imem,
                          otbn_imem_size * sizeof(uint32_t)) == kDifOtbnOk) {
    LOG_INFO("IMEM written");
  } else {
    LOG_ERROR("Error writing IMEM");
  }

  LOG_INFO("Verifying IMEM through readback");
  if (dif_otbn_imem_read(&otbn, 0, otbn_imem_readback,
                         otbn_imem_size * sizeof(uint32_t)) == kDifOtbnOk) {
    for (int i = 0; i < otbn_imem_size; ++i) {
      if (otbn_imem[i] != otbn_imem_readback[i]) {
        LOG_ERROR("IMEM mismatch at %d: 0x%08x written, 0x%08x read", i,
                  otbn_imem[i], otbn_imem_readback[i]);
      }
    }
  } else {
    LOG_ERROR("Error reading back IMEM");
  }

  LOG_INFO("Writing OTBN DMEM");
  if (dif_otbn_dmem_write(&otbn, 0, otbn_dmem,
                          otbn_dmem_size * sizeof(uint32_t)) == kDifOtbnOk) {
    LOG_INFO("DMEM written");
  } else {
    LOG_ERROR("Error writing DMEM");
  }

  LOG_INFO("Verifying DMEM through readback");
  if (dif_otbn_dmem_read(&otbn, 0, otbn_dmem_readback,
                         otbn_dmem_size * sizeof(uint32_t)) == kDifOtbnOk) {
    for (int i = 0; i < otbn_dmem_size; ++i) {
      if (otbn_dmem[i] != otbn_dmem_readback[i]) {
        LOG_ERROR("DMEM mismatch at %d: 0x%x written, 0x%x read", i,
                  otbn_dmem[i], otbn_dmem_readback[i]);
      }
    }
  } else {
    LOG_ERROR("Error reading back DMEM");
  }

  LOG_INFO("Starting OTBN ...");
  dif_otbn_start(&otbn);

  bool busy = true;
  while (busy) {
    if (!dif_otbn_is_busy(&otbn, &busy)) {
      busy = false;
    }
  }
  if (dif_otbn_dmem_read(&otbn, 0, otbn_dmem_readback,
                         otbn_dmem_size * sizeof(uint32_t)) != kDifOtbnOk) {
    LOG_ERROR("Error reading back DMEM");
  }
  LOG_INFO("OTBN finished its operation");
}

void check(size_t size, const uint32_t *data, const uint32_t *expected) {
  LOG_INFO("Reading back OTBN DMEM after processing");
  int errors = 0;
  for (int i = 0; i < size; i++) {
    if (data[i] != expected[i]) {
      errors++;
    }
  }
  if (errors > 0) {
    LOG_ERROR("Unexpected result, %d error(s)", errors);
    for (int i = 0; i < size; i++) {
      LOG_INFO("  [%02x] read: %08x expected: %08x", i, data[i], expected[i]);
    }
  } else {
    LOG_INFO("Result correct!");
  }
}

void test_mul() {
#include "program_mul.h"

  // DMEM must be 256b words!
  static const uint32_t data[32] = {
      // Word 0, op A
      0xB986BF4C,
      0xD3EB86EB,
      0x201DDDCF,
      0xAE35732E,
      0xAC0E011B,
      0x603A253C,
      0x17F7F2F2,
      0xCC3F07BF,
      // Word 1, op B
      0x37FD474E,
      0xAEBC5362,
      0x7C19ACF7,
      0x8C4660FB,
      0x913308D2,
      0xE0AF2287,
      0x38458651,
      0xE84DE529,
      // Word 2, result
      0x00000000,
      0x00000000,
      0x00000000,
      0x00000000,
      0x00000000,
      0x00000000,
      0x00000000,
      0x00000000,
      // Word 3, result
      0x00000000,
      0x00000000,
      0x00000000,
      0x00000000,
      0x00000000,
      0x00000000,
      0x00000000,
      0x00000000,
  };

  static const uint32_t result_expected[32] = {
      // Word 0, op A
      0xB986BF4C,
      0xD3EB86EB,
      0x201DDDCF,
      0xAE35732E,
      0xAC0E011B,
      0x603A253C,
      0x17F7F2F2,
      0xCC3F07BF,
      // Word 1, op B
      0x37FD474E,
      0xAEBC5362,
      0x7C19ACF7,
      0x8C4660FB,
      0x913308D2,
      0xE0AF2287,
      0x38458651,
      0xE84DE529,
      // Word 2, result
      0x48385D28,
      0xB96BA8A3,
      0xC09DCD8B,
      0x25240D7D,
      0x26BF6CD7,
      0x7E831234,
      0x24CD1C7D,
      0x6C2BA57B,
      // Word 3, result
      0x24892710,
      0xFF85C501,
      0x49A2E079,
      0x26BAE148,
      0x83824BBB,
      0x92266A87,
      0xC71E59A4,
      0xB95744CF,
  };

  uint32_t result[32];

  LOG_INFO("++++ Run mul test ++++");

  run(sizeof(code) / sizeof(uint32_t), code, sizeof(data) / sizeof(uint32_t),
      data, result);

  check(sizeof(data) / sizeof(uint32_t), result, result_expected);
}

void test_random() {
#include "program_random.h"

  uint32_t data[32];

  LOG_INFO("++++ Run random test ++++");

  run(sizeof(code) / sizeof(uint32_t), code, sizeof(data) / sizeof(uint32_t),
      (const uint32_t *)data, data);

  LOG_INFO("Does this look random?");

  for (int i = 0; i < 8; i++) {
    LOG_INFO("  %08x %08x %08x %08x", data[i * 4 + 0], data[i * 4 + 1],
             data[i * 4 + 2], data[i * 4 + 3]);
  }
}

int main(int argc, char **argv) {
  uart_init(kUartBaudrate);
  base_set_stdout(uart_stdout);

  dif_otbn_config_t otbn_config = {
      .base_addr = mmio_region_from_addr(TOP_EARLGREY_OTBN_BASE_ADDR),
  };
  dif_otbn_init(&otbn_config, &otbn);

  LOG_INFO("Hello OTBN!");
  LOG_INFO("Built at: " __DATE__ ", " __TIME__);

  test_mul();
  test_random();

  LOG_INFO("done");
}
