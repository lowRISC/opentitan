// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/silicon_creator/rom/rom_epmp.h"

#include <stdbool.h>
#include <stdint.h>

#include "sw/device/lib/arch/device.h"
#include "sw/device/lib/base/abs_mmio.h"
#include "sw/device/lib/base/csr.h"
#include "sw/device/lib/base/memory.h"
#include "sw/device/lib/base/stdasm.h"
#include "sw/device/lib/dif/dif_pinmux.h"
#include "sw/device/lib/dif/dif_sram_ctrl.h"
#include "sw/device/lib/runtime/hart.h"
#include "sw/device/lib/runtime/ibex.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/runtime/print.h"
#include "sw/device/lib/testing/pinmux_testutils.h"
#include "sw/device/lib/testing/test_framework/status.h"
#include "sw/device/silicon_creator/lib/base/sec_mmio.h"
#include "sw/device/silicon_creator/lib/drivers/flash_ctrl.h"
#include "sw/device/silicon_creator/lib/drivers/uart.h"
#include "sw/device/silicon_creator/lib/epmp_test_unlock.h"
#include "sw/device/silicon_creator/rom/rom_epmp.h"

#include "flash_ctrl_regs.h"  // Generated.
#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

/**
 * ROM ePMP test.
 *
 * This test uses the ROM linker script and ePMP setup code to initialize
 * its own ePMP configuration and then attempts to execute instructions in
 * various address spaces. Typically execution in these address spaces should be
 * blocked unless the unlock function has been called with a region containing
 * the address of the access.
 */

/**
 * Get the value of the `mcause` register.
 *
 * @returns The encoded interrupt or exception cause.
 */
static uint32_t get_mcause(void) {
  uint32_t mcause;
  CSR_READ(CSR_REG_MCAUSE, &mcause);
  return mcause;
}

/**
 * Get the value of the `mepc` register.
 *
 * @returns The value of the machine exception program counter.
 */
static uint32_t get_mepc(void) {
  uint32_t mepc;
  CSR_READ(CSR_REG_MEPC, &mepc);
  return mepc;
}

/**
 * Set the value of the `mepc` register.
 *
 * After an exception has been handled execution will be resumed at the address
 * contained within `mepc`.
 *
 * @param pc The value to set the machine exception program counter to.
 */
static void set_mepc(uint32_t pc) { CSR_WRITE(CSR_REG_MEPC, pc); }

/**
 * Interrupt handlers.
 *
 * If operating correctly this test should only trigger exceptions. Interrupts
 * are therefore not recovered.
 */
void rom_nmi_handler(void) { wait_for_interrupt(); }
void rom_interrupt_handler(void) { wait_for_interrupt(); }

/**
 * The type of last exception (if any) received.
 *
 * Set by the exception handler.
 */
volatile ibex_exc_t exception_received = 0;

/**
 * The `mepc` value for the last exception (if any) received.
 *
 * Set by the exception handler.
 */
volatile uintptr_t exception_pc = 0;

/**
 * Exception handler.
 *
 * Handle instruction access faults and illegal instructions by setting
 * `exception_received` and `exception_pc` and then returning to the code
 * that jumped (via a call) to the offending instruction.
 *
 * This will likely only work correctly if the instruction exception was
 * caused by a jump from `execute` to an invalid instruction (whether illegal
 * or inaccessible).
 *
 * For all other exceptions hang (could also shutdown) so as not to hide them.
 */
void rom_exception_handler(void) __attribute__((interrupt));
void rom_exception_handler(void) {
  uint32_t mcause = get_mcause();
  if (mcause == kIbexExcInstrAccessFault ||
      mcause == kIbexExcIllegalInstrFault) {
    exception_received = (ibex_exc_t)mcause;
    exception_pc = get_mepc();

    // Return to caller.
    uintptr_t ret = (uintptr_t)__builtin_return_address(0);
    set_mepc((uint32_t)ret);
    return;
  }

  // Wait forever if an unexpected exception is encountered.
  wait_for_interrupt();
}

/**
 * Attempt to execute the code at `pc` by calling it like a function.
 *
 * Typically the contents of `pc` should be an invalid instruction such
 * as an all zero value. In this case if execution was blocked by PMP an
 * instruction fault exception will be raised. If however execution was
 * allowed then an illegal instruction exception will be raised instead.
 *
 * The interrupt handler will arrange for control to be returned to the
 * caller on encountering either an instruction fault or illegal
 * instruction error so this function will report a result in either
 * case.
 *
 * @param pc The address of the instruction to try and execute.
 * @param expect The expected exception that will be raised.
 * @returns Whether the expected exception was raised at the correct PC.
 */
static bool execute(const void *pc, ibex_exc_t expect) {
  exception_pc = 0;
  exception_received = kIbexExcMax;

  // Jump to the target PC.
  //
  // Using a `call` here (`jal` or `jalr`) sets the return address (`ra`)
  // register. When an exception is raised the interrupt handler will recover
  // by restarting execution at the address in `ra` thereby making it appear
  // as if the call returned normally.
  //
  //   ...
  //   jal ra, pc # <- Set return address and jump to pc.
  //   ...        # <- Interrupt handler restarts execution at the next
  //              #    instruction in the caller, here.
  //
  // pc:
  //   unimp      # <- Illegal instruction or access fault. Enter interrupt
  //                   handler.
  //
  ((void (*)(void))pc)();

  // Be careful to ensure that the exception was raised when trying to
  // execute `pc` just in case a valid instruction is actually executed
  // and then execution continued to a point where an exception is
  // raised.
  if (exception_received != kIbexExcMax && exception_pc != (uintptr_t)pc) {
    return false;
  }
  return exception_received == expect;
}

/**
 * An instruction that has all bits set. This value is specifically chosen to
 * match an erased flash.
 *
 * Attempts to execute this instruction, `unimp`, will result in an illegal
 * instruction exception.
 *
 * Note that if compressed instructions are enabled only the first two bytes
 * will be decoded (as `c.unimp`).
 */
static const uint32_t kUnimpInstruction = UINT32_MAX;

/**
 * Illegal instruction residing in .rodata.
 */
static const uint32_t illegal_ins_ro[] = {
    kUnimpInstruction,
};

/**
 * Illegal instruction residing in .bss.
 */
static uint32_t illegal_ins_rw[] = {
    0,
};

/**
 * Report whether the given pointer points to a location with the provided
 * address space.
 *
 * @param ptr Pointer to test.
 * @param start Address of the start of the address space.
 * @param size The size of the address space in bytes.
 * @returns Whether the pointer is in the address space.
 */
static bool is_in_address_space(const void *ptr, uintptr_t start,
                                uintptr_t size) {
  return (uintptr_t)ptr >= start && (uintptr_t)ptr < (start + size);
}

/**
 * Set to false if a test fails.
 */
static bool passed = false;

/**
 * Custom CHECK macro to assert a condition that if false should cause the
 * test to fail. Note: we can't use the normal CHECK macro because it tries to
 * write to the DV address space but that is locked by the ePMP configuration.
 */
#define CHECK(condition)                  \
  if (!(condition)) {                     \
    LOG_ERROR("CHECK-fail: " #condition); \
    passed = false;                       \
  }

/**
 * Test that .rodata in the ROM is not executable.
 */
static void test_noexec_rodata(void) {
  CHECK(is_in_address_space(illegal_ins_ro, TOP_EARLGREY_ROM_CTRL_ROM_BASE_ADDR,
                            TOP_EARLGREY_ROM_CTRL_ROM_SIZE_BYTES));
  CHECK(execute(illegal_ins_ro, kIbexExcInstrAccessFault));
}

/**
 * Test that the .bss section in RAM is not executable.
 */
static void test_noexec_rwdata(void) {
  dif_sram_ctrl_t sram_ctrl;
  CHECK(dif_sram_ctrl_init(
            mmio_region_from_addr(TOP_EARLGREY_SRAM_CTRL_MAIN_REGS_BASE_ADDR),
            &sram_ctrl) == kDifOk);
  CHECK(dif_sram_ctrl_exec_set_enabled(&sram_ctrl, kDifToggleEnabled) ==
        kDifOk);
  CHECK(is_in_address_space(illegal_ins_rw, TOP_EARLGREY_RAM_MAIN_BASE_ADDR,
                            TOP_EARLGREY_RAM_MAIN_SIZE_BYTES));
  CHECK(execute(illegal_ins_rw, kIbexExcInstrAccessFault));
}

/**
 * Test that eFlash is not executable.
 */
static void test_noexec_eflash(void) {
  // Ideally we'd check all of eFlash but that takes a very long time in
  // simulation. Instead, check the first and last words are not executable and
  // check a sample of other addresses.
  uint32_t *eflash = (uint32_t *)TOP_EARLGREY_EFLASH_BASE_ADDR;
  size_t eflash_len = TOP_EARLGREY_EFLASH_SIZE_BYTES / sizeof(eflash[0]);
  CHECK(execute(&eflash[0], kIbexExcInstrAccessFault));
  CHECK(execute(&eflash[eflash_len - 1], kIbexExcInstrAccessFault));

  // Step size is picked arbitrarily but should provide a reasonable sample of
  // addresses.
  size_t step = eflash_len / 999;
  for (size_t i = step; i < eflash_len; i += step) {
    if (!execute(&eflash[i], kIbexExcInstrAccessFault)) {
      LOG_ERROR("eflash execution not blocked @ %p", &eflash[i]);
      passed = false;
      break;
    }
  }
}

/**
 * Test that the MMIO address space (specifically the retention RAM) is not
 * executable.
 */
static void test_noexec_mmio(void) {
  // Note: execution of retention RAM always fails regardless of controller or
  // ePMP configurations however it doesn't hurt to check it anyway.
  dif_sram_ctrl_t ret_ram_ctrl;
  CHECK(dif_sram_ctrl_init(mmio_region_from_addr(
                               TOP_EARLGREY_SRAM_CTRL_RET_AON_REGS_BASE_ADDR),
                           &ret_ram_ctrl) == kDifOk);
  CHECK(dif_sram_ctrl_exec_set_enabled(&ret_ram_ctrl, kDifToggleEnabled) ==
        kDifOk);
  uint32_t *ret_ram = (uint32_t *)TOP_EARLGREY_RAM_RET_AON_BASE_ADDR;
  size_t ret_ram_len = TOP_EARLGREY_RAM_RET_AON_SIZE_BYTES / sizeof(ret_ram[0]);
  ret_ram[0] = kUnimpInstruction;
  CHECK(execute(&ret_ram[0], kIbexExcInstrAccessFault));
  ret_ram[ret_ram_len - 1] = kUnimpInstruction;
  CHECK(execute(&ret_ram[ret_ram_len - 1], kIbexExcInstrAccessFault));
}

/**
 * Test the function used to unlock execution of the ROM extension.
 *
 * Unlock a section of eFlash to simulate the unlocking of the ROM_EXT text.
 * Accesses within the unlocked region should execute (and generate an illegal
 * instruction exception in this case) while accesses outside the unlocked
 * region should still fail with an instruction access fault exception.
 *
 * @param epmp The ePMP state to update.
 */
static void test_unlock_exec_eflash(void) {
  // Define a region to unlock (this is somewhat arbitrary but must be word-
  // aligned and beyond the ROM region, since this same image is placed in the
  // flash).
  uint32_t *eflash = (uint32_t *)TOP_EARLGREY_EFLASH_BASE_ADDR;
  size_t eflash_len = TOP_EARLGREY_EFLASH_SIZE_BYTES / sizeof(eflash[0]);
  uint32_t *image = &eflash[eflash_len / 5];
  size_t image_len = eflash_len / 7;
  epmp_region_t region = {.start = (uintptr_t)&image[0],
                          .end = (uintptr_t)&image[image_len]};

  // Unlock execution of the region and check that the same changes are made
  // to the ePMP state.
  rom_epmp_unlock_rom_ext_rx(region);
  CHECK(epmp_state_check() == kErrorOk);

  // Verify that execution within the region succeeds.
  // The image must consist of `unimp` instructions so that an illegal
  // instruction exception is generated. Because the region is not written and
  // tests begin with the flash erased, this instruction is expected to be
  // UINT32_MAX.
  CHECK(image[0] == kUnimpInstruction);
  CHECK(execute(&image[0], kIbexExcIllegalInstrFault));
  CHECK(image[image_len - 1] == kUnimpInstruction);
  CHECK(execute(&image[image_len - 1], kIbexExcIllegalInstrFault));

  // Verify that execution just outside the region still fails.
  CHECK(execute(&image[-1], kIbexExcInstrAccessFault));
  CHECK(execute(&image[image_len], kIbexExcInstrAccessFault));
}

void rom_main(void) {
  // Initialize global variables here so that they don't end up in the .data
  // section since OpenTitan ROM does not have one.
  passed = true;
  exception_received = kIbexExcMax;
  illegal_ins_rw[0] = kUnimpInstruction;

  // Initialize sec_mmio.
  sec_mmio_init();

  // Configure debug ROM ePMP entry.
  rom_epmp_config_debug_rom(kLcStateProd);

  // Initialize pinmux configuration so we can use the UART.
  dif_pinmux_t pinmux;
  OT_DISCARD(dif_pinmux_init(
      mmio_region_from_addr(TOP_EARLGREY_PINMUX_AON_BASE_ADDR), &pinmux));
  pinmux_testutils_init(&pinmux);

  // Enable execution of code in flash.
  flash_ctrl_init();
  flash_ctrl_exec_set(FLASH_CTRL_PARAM_EXEC_EN);
  SEC_MMIO_WRITE_INCREMENT(kFlashCtrlSecMmioInit + kFlashCtrlSecMmioExecSet);

  // Configure UART0 as stdout.
  uart_init(kUartNCOValue);
  base_set_stdout((buffer_sink_t){
      .data = NULL,
      .sink = uart_sink,
  });

  // Start the tests.
  LOG_INFO("Starting ROM ePMP functional test.");

  // Initialize shadow copy of the ePMP register configuration.
  memset(&epmp_state, 0, sizeof(epmp_state));
  rom_epmp_state_init(kLcStateProd);
  CHECK(epmp_state_check() == kErrorOk);

  // Test that execution outside the ROM text is blocked by default.
  test_noexec_rodata();
  test_noexec_rwdata();
  test_noexec_eflash();
  test_noexec_mmio();

  // Test that execution is unlocked for a sub-region of eFlash correctly.
  // Simulates the unlocking of the ROM extension text.
  test_unlock_exec_eflash();

  // The test of the ROM's ePMP configuration is now complete. Unlock the
  // DV address space so that the test result can be reported. Assumes that PMP
  // entry 6 is allocated for this purpose.
  CHECK(epmp_unlock_test_status());

  // Report the test status.
  //
  // Note that it is only now, after the DV address space has been unlocked that
  // we can signal that the test has started unfortunately.
  test_status_set(kTestStatusInTest);
  test_status_set(passed ? kTestStatusPassed : kTestStatusFailed);

  // Unreachable if reporting the test status correctly caused the
  // test to stop.
  while (true) {
    wait_for_interrupt();
  }
}
