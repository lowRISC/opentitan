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

// python test/programs.py -O carray -s mul_256x256
static const uint32_t otbn_imem [] = {
    0x00000213, // addi x4, x0, 0
    0x0000420b, // bn.lid x4, 0(x0)
    0x00100213, // addi x4, x0, 1
    0x0040420b, // bn.lid x4, 1(x0)
    0x00200213, // addi x4, x0, 2
    0x0080420b, // bn.lid x4, 2(x0)
    0x00300213, // addi x4, x0, 3
    0x00c0420b, // bn.lid x4, 3(x0)
    0x0010105b, // bn.mulqacc.z w0.0, w1.0, 0
    0x0810205b, // bn.mulqacc w0.1, w1.0, 64
    0x4210215b, // bn.mulqacc.so w2.l, w0.0, w1.1, 64
    0x1010005b, // bn.mulqacc w0.2, w1.0, 0
    0x0a10005b, // bn.mulqacc w0.1, w1.1, 0
    0x0410005b, // bn.mulqacc w0.0, w1.2, 0
    0x1810205b, // bn.mulqacc w0.3, w1.0, 64
    0x1210205b, // bn.mulqacc w0.2, w1.1, 64
    0x0c10205b, // bn.mulqacc w0.1, w1.2, 64
    0x6610215b, // bn.mulqacc.so w2.u, w0.0, w1.3, 64
    0x1a10005b, // bn.mulqacc w0.3, w1.1, 0
    0x1410005b, // bn.mulqacc w0.2, w1.2, 0
    0x0e10005b, // bn.mulqacc w0.1, w1.3, 0
    0x1c10205b, // bn.mulqacc w0.3, w1.2, 64
    0x561021db, // bn.mulqacc.so w3.l, w0.2, w1.3, 64
    0x7e1001db, // bn.mulqacc.so w3.u, w0.3, w1.3, 0
    0x00000213, // addi x4, x0, 0
    0x0000520b, // bn.sid x4, 0(x0)
    0x00100213, // addi x4, x0, 1
    0x0040520b, // bn.sid x4, 1(x0)
    0x00200213, // addi x4, x0, 2
    0x0080520b, // bn.sid x4, 2(x0)
    0x00300213, // addi x4, x0, 3
    0x00c0520b, // bn.sid x4, 3(x0)
};

static uint32_t otbn_imem_readback[sizeof(otbn_imem) / sizeof(uint32_t)];


// DMEM must be 256b words!
static const uint32_t otbn_dmem[] = {
    // Word 0, op A
    0xB986BF4C, 0xD3EB86EB, 0x201DDDCF, 0xAE35732E,
    0xAC0E011B, 0x603A253C, 0x17F7F2F2, 0xCC3F07BF,
    // Word 1, op B
    0x37FD474E, 0xAEBC5362, 0x7C19ACF7, 0x8C4660FB,
    0x913308D2, 0xE0AF2287, 0x38458651, 0xE84DE529,
    // Word 2, result
    0x00000000, 0x00000000, 0x00000000, 0x00000000,
    0x00000000, 0x00000000, 0x00000000, 0x00000000,
    // Word 3, result
    0x00000000, 0x00000000, 0x00000000, 0x00000000,
    0x00000000, 0x00000000, 0x00000000, 0x00000000,
};

static const uint32_t otbn_dmem_expected[] = {
    // Word 0, op A
    0xB986BF4C, 0xD3EB86EB, 0x201DDDCF, 0xAE35732E,
    0xAC0E011B, 0x603A253C, 0x17F7F2F2, 0xCC3F07BF,
    // Word 1, op B
    0x37FD474E, 0xAEBC5362, 0x7C19ACF7, 0x8C4660FB,
    0x913308D2, 0xE0AF2287, 0x38458651, 0xE84DE529,
    // Word 2, result
    0x48385D28, 0xB96BA8A3, 0xC09DCD8B, 0x25240D7D,
    0x26BF6CD7, 0x7E831234, 0x24CD1C7D, 0x6C2BA57B,
    // Word 3, result
    0x24892710, 0xFF85C501, 0x49A2E079, 0x26BAE148,
    0x83824BBB, 0x92266A87, 0xC71E59A4, 0xB95744CF,
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
      LOG_INFO("DMEM at 32b word %2d modified from 0x%08x to 0x%08x, expected 0x%08x", i,
               otbn_dmem[i], otbn_dmem_readback[i], otbn_dmem_expected[i]);
    }
  } else {
    LOG_ERROR("Error reading back DMEM");
  }

  LOG_INFO("done");
}
