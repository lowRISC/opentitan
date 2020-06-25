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

static const uint32_t otbn_imem [] = {
  0x00000293, // li	t0,0
  0x10000313, // li	t1,256
  0x0002a503, // loop: lw	a0,0(t0)
  0x00851793, // slli	a5,a0,0x8
  0x00ff06b7, // lui	a3,0xff0
  0x00d7f7b3, // and	a5,a5,a3
  0x000106b7, // lui	a3,0x10
  0x40855713, // srai	a4,a0,0x8
  0xf0068693, // addi	a3,a3,-256
  0x00d77733, // and	a4,a4,a3
  0x00e7e7b3, // or	a5,a5,a4
  0x01855713, // srli	a4,a0,0x18
  0x00e7e7b3, // or	a5,a5,a4
  0x01851513, // slli	a0,a0,0x18
  0x00a7e533, // or	a0,a5,a0
  0x00a2a023, // sw	a0,0(t0)
  0x00428293, // addi	t0,t0,4
  0xfc6292e3, // bne	t0,t1,8
  0x00000073, // ecall
};

static uint32_t otbn_imem_readback[sizeof(otbn_imem) / sizeof(uint32_t)];

// DMEM must be 256b words!
static const uint32_t otbn_dmem[] = {
    // Word 0, least significant to most significant 32b sub-word
    0x01234567, 0x89ABCDEF, 0xDEADBEEF, 0x42424242,
    0xDEADBEEF, 0x42424242, 0x01234567, 0x89ABCDEF,
};

static uint32_t otbn_dmem_readback[sizeof(otbn_dmem) / sizeof(uint32_t)];

int main(int argc, char **argv) {
  uart_init(kUartBaudrate);
  base_set_stdout(uart_stdout);

  dif_otbn_config_t otbn_config = {
      .base_addr = mmio_region_from_addr(TOP_EARLGREY_OTBN_BASE_ADDR),
  };
  dif_otbn_init(&otbn_config, &otbn);

  LOG_INFO("Hello OTBN!");
  LOG_INFO("Built at: " __DATE__ ", " __TIME__);

  LOG_INFO("Writing OTBN IMEM");
  if (dif_otbn_imem_write(&otbn, 0, &otbn_imem, sizeof(otbn_imem)) ==
      kDifOtbnOk) {
    LOG_INFO("IMEM written");
  } else {
    LOG_ERROR("Error writing IMEM");
  }

  LOG_INFO("Verifying IMEM through readback");
  if (dif_otbn_imem_read(&otbn, 0, &otbn_imem_readback,
                         sizeof(otbn_imem_readback)) == kDifOtbnOk) {
    for (int i = 0; i < sizeof(otbn_imem_readback) / sizeof(uint32_t); ++i) {
      if (otbn_imem[i] != otbn_imem_readback[i]) {
        LOG_ERROR("IMEM mismatch at %d: 0x%x written, 0x%x read", i,
                  otbn_imem[i], otbn_imem_readback[i]);
      }
    }
  } else {
    LOG_ERROR("Error reading back IMEM");
  }

  LOG_INFO("Writing OTBN DMEM");
  if (dif_otbn_dmem_write(&otbn, 0, &otbn_dmem, sizeof(otbn_dmem)) ==
      kDifOtbnOk) {
    LOG_INFO("DMEM written");
  } else {
    LOG_ERROR("Error writing DMEM");
  }

  LOG_INFO("Verifying DMEM through readback");
  if (dif_otbn_dmem_read(&otbn, 0, &otbn_dmem_readback,
                         sizeof(otbn_dmem_readback)) == kDifOtbnOk) {
    for (int i = 0; i < sizeof(otbn_dmem_readback) / sizeof(uint32_t); ++i) {
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

  LOG_INFO("OTBN finished its operation");

  LOG_INFO("Reading back OTBN DMEM after processing");
  if (dif_otbn_dmem_read(&otbn, 0, &otbn_dmem_readback,
                         sizeof(otbn_dmem_readback)) == kDifOtbnOk) {
    for (int i = 0; i < sizeof(otbn_dmem_readback) / sizeof(uint32_t); i++) {
      LOG_INFO("DMEM at 32b word %d modified from 0x%x to 0x%x", i,
               otbn_dmem[i], otbn_dmem_readback[i]);
    }
  } else {
    LOG_ERROR("Error reading back DMEM");
  }

  LOG_INFO("done");
}
