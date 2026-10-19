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
#include "sw/device/silicon_creator/lib/drivers/retention_sram.h"
#include "sw/device/silicon_creator/lib/nvm_ctrl.h"

// Triggering an uncorrectable RRAM ECC fault latches RRAM_CTRL's fatal_err
// alert sender (IsFatal = 1) until reset, so ignore OTTF alerts when booting
// into test_main().
OTTF_DEFINE_TEST_CONFIG(.ignore_alerts = true);

extern char _ottf_start_address[];

enum {
  // Unused NVM page in Slot A (256 KiB offset), well past the test binary and
  // well before the emulated info / OTTF scratch area at the end of Slot A.
  kCorruptOffset = 256 * 1024,
  kCorruptPageIdx = kCorruptOffset / NVM_BYTES_PER_PAGE,
  kCorruptWordAddr = kCorruptOffset / sizeof(uint32_t),

  // Number of faulting NVM load instruction cases recorded in retention SRAM
  // (`lw`, `c.lw`, `lh`, `lb`, `lhu`, `lbu`, and virtual-window `lbu`).
  kNumTestReadAccesses = 7,
};

static_assert(
    kNumTestReadAccesses <= ARRAYSIZE(((retention_sram_t *)0)->owner.reserved),
    "kNumTestReadAccesses exceeds retention_sram_t owner.reserved capacity.");

/**
 * Exercises the ROM's `nvm_exception_handler` across RISC-V load variants.
 *
 * During `rom_boot()`, the ROM configures `mtvec` to point to
 * `nvm_exception_handler` (in
 * `sw/device/silicon_creator/lib/rram_exc_handler.S`) and enables it via
 * `nvm_ecc_exc_handler_en = kHardenedBoolTrue`. Once the ROM jumps to the
 * standard OTTF entry point (`_ottf_start`), OTTF replaces `mtvec` with its own
 * trap vector and zeroes `.bss` (clearing `nvm_ecc_exc_handler_en`), so the
 * ROM's NVM exception handler is no longer active by the time `test_main()`
 * runs.
 *
 * By placing this function in `.rom_ext_immutable` and enabling
 * `CREATOR_SW_CFG_IMMUTABLE_ROM_EXT_EN` in OTP, `rom_boot()` invokes
 * `rom_ext_non_mutable()` as a function call immediately before jumping to
 * `_ottf_start`, while the ROM's `mtvec` and `nvm_ecc_exc_handler_en` state
 * are still active. Each load from the ECC-corrupted NVM word raises a
 * synchronous `LoadAccessFault` (`mcause = 5`) with `PHY_RELBL_ERR` set in
 * `RRAM_CTRL.FAULT_STATUS`. The ROM's `nvm_exception_handler` intercepts the
 * fault, clears `FAULT_STATUS`, decodes the faulting load instruction at
 * `mepc`, writes all-ones masked to the load width into the destination
 * register (`0xffffffff` for `lw`/`c.lw`/`lh`/`lb`, `0x0000ffff` for `lhu`, and
 * `0x000000ff` for `lbu`), and advances `mepc` to the next instruction.
 *
 * The resulting register values are saved into `retention_sram` so
 * `test_main()` can verify them after OTTF finishes booting.
 */
OT_USED OT_SECTION(".rom_ext_immutable") void rom_ext_non_mutable(void) {
  uint32_t *res = retention_sram_get()->owner.reserved;
  for (size_t i = 0; i < kNumTestReadAccesses; ++i) {
    res[i] = 0xdeadbeefu;
  }

  // Configure the test page with ECC and scrambling disabled (`kNvmPageCfgRaw`)
  // and write a 16-byte RRAM granule whose lower 64-bit half (`0x00000003`) has
  // Hamming distance 2 from the all-zero codeword (`ecc0 = 0x00` stored when
  // ECC is disabled). Note that `rram_ctrl` always enables bus-word address
  // infection (`addr_xor_en = MuBi4True`), which XORs each 32-bit word with its
  // word offset before writing to `rram_macro`; pre-XORing with
  // `kCorruptWordAddr + i` cancels the write-path address XOR so the raw macro
  // stores `0x00000000_00000003` with `ecc0 = 0x00`. Re-enabling ECC
  // (`kNvmPageCfgPlain`) without scrambling causes any subsequent load from
  // this granule to decode `{ecc=0x00, data=0x3}` via
  // `prim_secded_hamming_72_64_dec`, raising an uncorrectable 2-bit ECC fault
  // (`FAULT_STATUS.PHY_RELBL_ERR`).
  nvm_ctrl_data_region_protect(/*region=*/0, /*page_offset=*/kCorruptPageIdx,
                               /*num_pages=*/1, kNvmPagePermsReadWrite,
                               kNvmPageCfgRaw, /*lock=*/kHardenedBoolFalse);
  const uint32_t words[4] = {
      0x00000003u ^ ((uint32_t)kCorruptWordAddr + 0u),
      0x00000000u ^ ((uint32_t)kCorruptWordAddr + 1u),
      0x00000000u ^ ((uint32_t)kCorruptWordAddr + 2u),
      0x00000000u ^ ((uint32_t)kCorruptWordAddr + 3u),
  };
  if (nvm_ctrl_data_write(kCorruptOffset, ARRAYSIZE(words), words) !=
      kErrorOk) {
    return;
  }
  nvm_ctrl_data_region_protect(/*region=*/0, /*page_offset=*/kCorruptPageIdx,
                               /*num_pages=*/1, kNvmPagePermsReadWrite,
                               kNvmPageCfgPlain, /*lock=*/kHardenedBoolFalse);

  const uintptr_t phys_addr = NVM_DATA_BASE_ADDR + kCorruptOffset;
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
