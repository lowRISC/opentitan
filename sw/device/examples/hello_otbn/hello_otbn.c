// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/arch/device.h"
#include "sw/device/lib/base/log.h"
#include "sw/device/lib/runtime/hart.h"
#include "sw/device/lib/testing/test_status.h"
#include "sw/device/lib/uart.h"

#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/dif/dif_otbn.h"

static dif_otbn_t otbn;

#define OTBN_BASE_ADDR 0x50000000ULL

static const uint32_t otbn_imem [] = {
  0xDEADBEEF,
  0xABCD0123,
  0x42424242,
};

static uint32_t otbn_imem_readback [sizeof(otbn_imem)/sizeof(uint32_t)] = { 0 };

// DMEM must be 256b words!
static const uint32_t otbn_dmem [] = {
  // Word 0, least significant to most significant 32b sub-word
  0x01234567,
  0x89ABCDEF,
  0xDEADBEEF,
  0x42424242,
  0xDEADBEEF,
  0x42424242,
  0x01234567,
  0x89ABCDEF,
};

static uint32_t otbn_dmem_readback [sizeof(otbn_dmem)/sizeof(uint32_t)] = { 0 };

int main(int argc, char **argv) {
  uart_init(kUartBaudrate);
  base_set_stdout(uart_stdout);

  dif_otbn_config_t otbn_config = {.base_addr =
                                       mmio_region_from_addr(OTBN_BASE_ADDR)};
  dif_otbn_init(&otbn_config, &otbn);

  LOG_INFO("Hello OTBN!");
  LOG_INFO("Built at: " __DATE__ ", " __TIME__);

  LOG_INFO("Writing OTBN IMEM");
  if (dif_otbn_imem_write(&otbn, 0, &otbn_imem, sizeof(otbn_imem)) == kDifOtbnOk) {
    LOG_INFO("IMEM written");
  } else {
    LOG_ERROR("Error writing IMEM");
  }

  LOG_INFO("Verifying IMEM through readback");
  if (dif_otbn_imem_read(&otbn, 0, &otbn_imem_readback, sizeof(otbn_imem_readback)) == kDifOtbnOk) {
    for (int i = 0; i < sizeof(otbn_imem_readback)/sizeof(uint32_t); i++) {
      if (otbn_imem[i] != otbn_imem_readback[i]) {
        LOG_ERROR("IMEM mismatch at %d: 0x%x written, 0x%x read", i, otbn_imem[i], otbn_imem_readback[i]);
      }
    }
  } else {
    LOG_ERROR("Error reading back IMEM");
  }

  LOG_INFO("Writing OTBN DMEM");
  if (dif_otbn_dmem_write(&otbn, 0, &otbn_dmem, sizeof(otbn_dmem)) == kDifOtbnOk) {
    LOG_INFO("DMEM written");
  } else {
    LOG_ERROR("Error writing DMEM");
  }

  LOG_INFO("Verifying DMEM through readback");
  if (dif_otbn_dmem_read(&otbn, 0, &otbn_dmem_readback, sizeof(otbn_dmem_readback)) == kDifOtbnOk) {
    for (int i = 0; i < sizeof(otbn_dmem_readback)/sizeof(uint32_t); i++) {
      if (otbn_dmem[i] != otbn_dmem_readback[i]) {
        LOG_ERROR("DMEM mismatch at %d: 0x%x written, 0x%x read", i, otbn_dmem[i], otbn_dmem_readback[i]);
      }
    }
  } else {
    LOG_ERROR("Error reading back DMEM");
  }

  LOG_INFO("Starting OTBN ...");
  dif_otbn_start(&otbn);

  bool busy = false;
  do {
    if (!dif_otbn_is_busy(&otbn, &busy)) {
      busy = false;
    }
  } while (busy);

  LOG_INFO("OTBN finished its operation");

  LOG_INFO("Reading back OTBN DMEM after processing");
  if (dif_otbn_dmem_read(&otbn, 0, &otbn_dmem_readback, sizeof(otbn_dmem_readback)) == kDifOtbnOk) {
    for (int i = 0; i < sizeof(otbn_dmem_readback)/sizeof(uint32_t); i++) {
      LOG_INFO("DMEM at 32b word %d modified from 0x%x to 0x%x", i, otbn_dmem[i], otbn_dmem_readback[i]);
    }
  } else {
    LOG_ERROR("Error reading back DMEM");
  }

  LOG_INFO("done");
}
