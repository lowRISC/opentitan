// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/silicon_creator/rom/base_rom.h"

#include <stdbool.h>
#include <stdint.h>

#include "sw/device/silicon_creator/lib/drivers/alert.h"
#include "sw/device/silicon_creator/lib/drivers/ast.h"
#include "sw/device/silicon_creator/lib/drivers/ibex.h"
#include "sw/device/silicon_creator/lib/drivers/lifecycle.h"
#include "sw/device/silicon_creator/lib/drivers/otp.h"
#include "sw/device/silicon_creator/lib/drivers/pinmux.h"
#include "sw/device/silicon_creator/lib/drivers/retention_sram.h"
#include "sw/device/silicon_creator/lib/drivers/rnd.h"
#include "sw/device/silicon_creator/lib/drivers/rstmgr.h"
#include "sw/device/silicon_creator/lib/drivers/uart.h"
#include "sw/device/silicon_creator/lib/drivers/watchdog.h"
#include "sw/device/silicon_creator/rom/base_rom_epmp.h"
#include "sw/device/silicon_creator/rom/sigverify_keys_rsa.h"
#include "sw/lib/sw/device/arch/device.h"
#include "sw/lib/sw/device/base/bitfield.h"
#include "sw/lib/sw/device/base/csr.h"
#include "sw/lib/sw/device/base/hardened.h"
#include "sw/lib/sw/device/base/macros.h"
#include "sw/lib/sw/device/base/memory.h"
#include "sw/lib/sw/device/base/stdasm.h"
#include "sw/lib/sw/device/silicon_creator/base/boot_measurements.h"
#include "sw/lib/sw/device/silicon_creator/base/sec_mmio.h"
#include "sw/lib/sw/device/silicon_creator/cfi.h"
#include "sw/lib/sw/device/silicon_creator/dbg_print.h"
#include "sw/lib/sw/device/silicon_creator/epmp_state.h"
#include "sw/lib/sw/device/silicon_creator/error.h"
#include "sw/lib/sw/device/silicon_creator/rom_patch.h"
#include "sw/lib/sw/device/silicon_creator/shutdown.h"
#include "sw/lib/sw/device/silicon_creator/sigverify/sigverify.h"

#include "hw/top_darjeeling/sw/autogen/top_darjeeling.h"
#include "otp_ctrl_regs.h"

/**
 * Type alias for the second stage ROM entry point.
 */
typedef void second_rom_entry_point(void);

/**
 * Table of forward branch Control Flow Integrity (CFI) counters.
 *
 * Columns: Name, Initital Value.
 *
 * Each counter is indexed by Name. The Initial Value is used to initialize the
 * counters with unique values with a good hamming distance. The values are
 * restricted to 11-bit to be able use immediate load instructions.

 * Encoding generated with
 * $ ./util/design/sparse-fsm-encode.py -d 6 -m 3 -n 16 \
 *   -s 8806821418 --language=c
 *
 * Minimum Hamming distance: 6
 * Maximum Hamming distance: 13
 * Minimum Hamming weight: 6
 * Maximum Hamming weight: 9
 */
// clang-format off
#define ROM_CFI_FUNC_COUNTERS_TABLE(X) \
  X(kCfiBaseRomMain,         0x426) \
  X(kCfiBaseRomInit,         0x2dd) \
  X(kCfiSecondRomBoot,       0x740) \
  X(kCfiSecondRomPatch,      0x3aa)
// clang-format on

// Define counters and constant values required by the CFI counter macros.
CFI_DEFINE_COUNTERS(rom_counters, ROM_CFI_FUNC_COUNTERS_TABLE);

// Life cycle state of the chip.
lifecycle_state_t lc_state = (lifecycle_state_t)0;

OT_ALWAYS_INLINE
OT_WARN_UNUSED_RESULT
static rom_error_t rom_irq_error(void) {
  uint32_t mcause;
  CSR_READ(CSR_REG_MCAUSE, &mcause);
  // Shuffle the mcause bits into the uppermost byte of the word and report
  // the cause as kErrorInterrupt.
  // Based on the ibex verilog, it appears that the most significant bit
  // indicates whether the cause is an exception (0) or external interrupt (1),
  // and the 5 least significant bits indicate which exception/interrupt.
  //
  // Preserve the MSB and shift the 7 LSBs into the upper byte.
  // (we preserve 7 instead of 5 because the verilog hardcodes the unused bits
  // as zero and those would be the next bits used should the number of
  // interrupt causes increase).
  mcause = (mcause & 0x80000000) | ((mcause & 0x7f) << 24);
  return kErrorInterrupt + mcause;
}

/**
 * Performs once-per-boot initialization of ROM modules and peripherals.
 */
OT_WARN_UNUSED_RESULT
static rom_error_t base_rom_init(void) {
  CFI_FUNC_COUNTER_INCREMENT(rom_counters, kCfiBaseRomInit, 1);
  sec_mmio_init();
  // Initialize pinmux configuration so we can use the UART.
  pinmux_init();
  // Configure UART0 as stdout.
  uart_init(kUartNCOValue);

  dbg_printf("Starting Base ROM\n");

  // There are no conditional checks before writing to this CSR because it is
  // expected that if relevant Ibex countermeasures are disabled, this will
  // result in a nop.
  CSR_WRITE(CSR_REG_SECURESEED, rnd_uint32());

  // Write the OTP value to bits 0 to 5 of the cpuctrl CSR.
  uint32_t cpuctrl_csr;
  CSR_READ(CSR_REG_CPUCTRL, &cpuctrl_csr);
  cpuctrl_csr = bitfield_field32_write(
      cpuctrl_csr, (bitfield_field32_t){.mask = 0x3f, .index = 0},
      otp_read32(OTP_CTRL_PARAM_CREATOR_SW_CFG_CPUCTRL_OFFSET));
  CSR_WRITE(CSR_REG_CPUCTRL, cpuctrl_csr);

  lc_state = lifecycle_state_get();

  // Re-initialize the watchdog timer.
  watchdog_init(lc_state);
  SEC_MMIO_WRITE_INCREMENT(kWatchdogSecMmioInit);

  // Initialize the shutdown policy.
  HARDENED_RETURN_IF_ERROR(shutdown_init(lc_state));

  // Initialize in-memory copy of the ePMP register configuration.
  base_rom_epmp_state_init();
  HARDENED_RETURN_IF_ERROR(epmp_state_check());

  // Initialize the retention RAM based on the reset reason and the OTP value.
  // Note: Retention RAM is always reset on PoR regardless of the OTP value.
  uint32_t reset_reasons = rstmgr_reason_get();
  uint32_t reset_mask =
      (1 << kRstmgrReasonPowerOn) |
      otp_read32(OTP_CTRL_PARAM_CREATOR_SW_CFG_RET_RAM_RESET_MASK_OFFSET);
  if ((reset_reasons & reset_mask) != 0) {
    retention_sram_init();
    retention_sram_get()->version = kRetentionSramVersion1;
  }
  // Store the reset reason in retention RAM and clear the register.
  retention_sram_get()->creator.reset_reasons = reset_reasons;
  rstmgr_reason_clear(reset_reasons);

  sec_mmio_check_values(rnd_uint32());
  sec_mmio_check_counters(/*expected_check_count=*/1);

  CFI_FUNC_COUNTER_INCREMENT(rom_counters, kCfiBaseRomInit, 2);
  return kErrorOk;
}

/**
 * Patches second ROM code with an OTP ROM patch.
 *
 * If a patch is successfully applied, the patch digest
 * is stored into the boot measurement section.
 *
 * @return Result of the second ROM patching.
 */
static rom_error_t second_rom_patch(void) {
  CFI_FUNC_COUNTER_INCREMENT(rom_counters, kCfiSecondRomPatch, 1);
  rom_patch_info_t latest_patch = rom_patch_latest(NULL);

  do {
    /* We could not find a latest patch, we're done */
    if (latest_patch.addr == kRomPatchInvalidAddr) {
      break;
    }

    hmac_digest_t patch_digest;
    rom_error_t error = rom_patch_apply(&latest_patch, &patch_digest);

    /* The latest patch could not be applied, let's try the next one */
    if (launder32(error) != kErrorOk) {
      latest_patch = rom_patch_latest(&latest_patch);
      continue;
    }
    HARDENED_CHECK_EQ(error, kErrorOk);

    /* Latest patch applied, let's store the patch measurement */
    static_assert(sizeof(boot_measurements.rom_patch) == sizeof(patch_digest),
                  "Unexpected ROM patch digest size.");
    memcpy(&boot_measurements.rom_patch, &patch_digest,
           sizeof(boot_measurements.rom_patch));
  } while (false);

  CFI_FUNC_COUNTER_INCREMENT(rom_counters, kCfiSecondRomPatch, 2);
  return kErrorOk;
}

// This symbol is defined in `base_rom.ld` and describes the location of the
// second ROM entry point.
extern char _second_rom_boot_address[];

/**
 * Attempts to boot 2nd stage ROM.
 *
 * @return Result of the last attempt.
 */
OT_WARN_UNUSED_RESULT
static rom_error_t second_rom_boot(void) {
  CFI_FUNC_COUNTER_PREPCALL(rom_counters, kCfiSecondRomBoot, 1,
                            kCfiSecondRomPatch);
  HARDENED_RETURN_IF_ERROR(second_rom_patch());
  CFI_FUNC_COUNTER_INCREMENT(rom_counters, kCfiSecondRomBoot, 3);
  CFI_FUNC_COUNTER_CHECK(rom_counters, kCfiSecondRomPatch, 3);

  CFI_FUNC_COUNTER_INCREMENT(rom_counters, kCfiSecondRomBoot, 4);
  uintptr_t entry_point = ((uintptr_t)_second_rom_boot_address) + 0x80;

  // Configure ePMP for the second stage ROM
  base_rom_epmp_unlock_second_rom_rx();
  // TODO: base_rom_epmp_unlock_second_rom_patch_ram(patch);

  // Check the ePMP state again
  HARDENED_RETURN_IF_ERROR(epmp_state_check());
  CFI_FUNC_COUNTER_INCREMENT(rom_counters, kCfiSecondRomBoot, 5);

  // Re-initialize mtvec
  CSR_WRITE(CSR_REG_MTVEC, ((uintptr_t)_second_rom_boot_address) | 1);

  // Jump to the second rom entry point
  dbg_printf("Jumping to 2nd stage ROM\n");
  CFI_FUNC_COUNTER_INCREMENT(rom_counters, kCfiSecondRomBoot, 6);
  ((second_rom_entry_point *)entry_point)();

  return kErrorRomBootFailed;
}

void base_rom_main(void) {
  CFI_FUNC_COUNTER_INIT(rom_counters, kCfiBaseRomMain);

  CFI_FUNC_COUNTER_PREPCALL(rom_counters, kCfiBaseRomMain, 1, kCfiBaseRomInit);
  SHUTDOWN_IF_ERROR(base_rom_init());
  CFI_FUNC_COUNTER_INCREMENT(rom_counters, kCfiBaseRomMain, 3);
  CFI_FUNC_COUNTER_CHECK(rom_counters, kCfiBaseRomInit, 3);

  // `second_rom_boot` will not return unless there is an error.
  CFI_FUNC_COUNTER_PREPCALL(rom_counters, kCfiBaseRomMain, 4,
                            kCfiSecondRomBoot);
  shutdown_finalize(second_rom_boot());
}

void rom_interrupt_handler(void) {
  register rom_error_t error asm("a0") = rom_irq_error();
  asm volatile("tail shutdown_finalize;" ::"r"(error));
  OT_UNREACHABLE();
}

// We only need a single handler for all ROM interrupts, but we want to
// keep distinct symbols to make writing tests easier.  In the ROM,
// alias all interrupt handler symbols to the single handler.
OT_ALIAS("rom_interrupt_handler")
noreturn void rom_exception_handler(void);

OT_ALIAS("rom_interrupt_handler")
noreturn void rom_nmi_handler(void);
