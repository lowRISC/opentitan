// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include <stdint.h>

#include "sw/device/lib/base/hardened.h"
#include "sw/device/lib/base/macros.h"
#include "sw/device/lib/base/multibits.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"
#include "sw/device/silicon_creator/lib/drivers/flash_ctrl.h"
#include "sw/device/silicon_creator/lib/drivers/retention_sram.h"

#include "flash_ctrl_regs.h"
#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

OTTF_DEFINE_TEST_CONFIG();

extern char _ottf_start_address[];

enum {
  // Unused flash page in Bank 0 (256 KiB offset), well past the test binary
  // and well before the OTTF non-volatile scratch area at the end of Bank 0.
  kCorruptPageIdx = 128,
  kCorruptOffset = kCorruptPageIdx * FLASH_CTRL_PARAM_BYTES_PER_PAGE,
};

OT_SECTION(".rom_ext_immutable")
void rom_ext_non_mutable(void) {
  uint32_t *res = retention_sram_get()->owner.reserved;
  for (size_t i = 0; i < 7; ++i) {
    res[i] = 0xdeadbeefu;
  }

  // Enable read, write, erase, scrambling, and ECC on the test page.
  flash_ctrl_data_region_protect(
      /*region=*/0, /*page_offset=*/kCorruptPageIdx, /*num_pages=*/1,
      (flash_ctrl_perms_t){
          .read = kMultiBitBool4True,
          .write = kMultiBitBool4True,
          .erase = kMultiBitBool4True,
      },
      (flash_ctrl_cfg_t){
          .scrambling = kMultiBitBool4True,
          .ecc = kMultiBitBool4True,
          .he = kMultiBitBool4False,
      },
      /*lock=*/kHardenedBoolFalse);

  // Erase the page, then double-write the first word without erasing to
  // corrupt its ECC.
  if (flash_ctrl_data_erase(kCorruptOffset, kFlashCtrlEraseTypePage) !=
      kErrorOk) {
    return;
  }
  uint32_t word = 0x5a5a5a5au;
  if (flash_ctrl_data_write(kCorruptOffset, /*word_count=*/1, &word) !=
      kErrorOk) {
    return;
  }
  word = ~word;
  if (flash_ctrl_data_write(kCorruptOffset, /*word_count=*/1, &word) !=
      kErrorOk) {
    return;
  }

  const uintptr_t phys_addr = TOP_EARLGREY_EFLASH_BASE_ADDR + kCorruptOffset;
  const uintptr_t virt_addr = (uintptr_t)_ottf_start_address + kCorruptOffset;

  // Test uncompressed 32-bit word load (lw).
  uint32_t val_lw = 0x12345678u;
  asm volatile(
      ".option push\n"
      ".option norvc\n"
      "lw %0, 0(%1)\n"
      ".option pop\n"
      : "+r"(val_lw)
      : "r"(phys_addr));

  // Test compressed 16-bit word load (c.lw).
  register uint32_t val_clw asm("a0") = phys_addr;
  asm volatile(
      ".option push\n"
      ".option rvc\n"
      "c.lw %0, 0(%0)\n"
      ".option pop\n"
      : "+r"(val_clw));

  // Test sign-extended halfword and byte loads (lh, lb).
  uint32_t val_lh = 0x12345678u;
  asm volatile("lh %0, 0(%1)" : "+r"(val_lh) : "r"(phys_addr));

  uint32_t val_lb = 0x12345678u;
  asm volatile("lb %0, 0(%1)" : "+r"(val_lb) : "r"(phys_addr));

  // Test zero-extended halfword and byte loads (lhu, lbu) with non-zero upper
  // bits in the destination register beforehand.
  uint32_t val_lhu = 0x12345678u;
  asm volatile("lhu %0, 0(%1)" : "+r"(val_lhu) : "r"(phys_addr));

  uint32_t val_lbu = 0x12345678u;
  asm volatile("lbu %0, 0(%1)" : "+r"(val_lbu) : "r"(phys_addr));

  // Test zero-extended byte load through the ROM_EXT virtual window.
  uint32_t val_virt_lbu = 0x12345678u;
  asm volatile("lbu %0, 0(%1)" : "+r"(val_virt_lbu) : "r"(virt_addr));

  res[0] = val_lw;
  res[1] = val_clw;
  res[2] = val_lh;
  res[3] = val_lb;
  res[4] = val_lhu;
  res[5] = val_lbu;
  res[6] = val_virt_lbu;
}

bool test_main(void) {
  const uint32_t *res = retention_sram_get()->owner.reserved;
  LOG_INFO(
      "lw=0x%08x c.lw=0x%08x lh=0x%08x lb=0x%08x lhu=0x%08x lbu=0x%08x "
      "virt_lbu=0x%08x",
      res[0], res[1], res[2], res[3], res[4], res[5], res[6]);

  CHECK(res[0] == 0xffffffffu, "lw expected 0xffffffff, got 0x%08x", res[0]);
  CHECK(res[1] == 0xffffffffu, "c.lw expected 0xffffffff, got 0x%08x", res[1]);
  CHECK(res[2] == 0xffffffffu, "lh expected 0xffffffff, got 0x%08x", res[2]);
  CHECK(res[3] == 0xffffffffu, "lb expected 0xffffffff, got 0x%08x", res[3]);
  CHECK(res[4] == 0x0000ffffu, "lhu expected 0x0000ffff, got 0x%08x", res[4]);
  CHECK(res[5] == 0x000000ffu, "lbu expected 0x000000ff, got 0x%08x", res[5]);
  CHECK(res[6] == 0x000000ffu, "virt lbu expected 0x000000ff, got 0x%08x",
        res[6]);

  return true;
}
