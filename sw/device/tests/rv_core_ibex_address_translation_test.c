// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/base/csr.h"
#include "sw/device/lib/base/memory.h"
#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/dif/dif_rv_core_ibex.h"
#include "sw/device/lib/runtime/ibex.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_isrs.h"
#include "sw/device/lib/testing/test_framework/ottf_macros.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"
#include "sw/device/silicon_creator/lib/epmp.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

#define TEST_STR "Hello there, WHaT 1S Y0Ur N@ME?"
#define EXPECTED_RESULT_MAKE_LOWER_CASE "hello there, what 1s y0ur n@me?"
#define EXPECTED_RESULT_GET_NAME "My name is Titan, Open Titan"

OTTF_DEFINE_TEST_CONFIG();

// A function which takes a string as its only argument.
typedef void (*str_fn_t)(char *);

/**
 * A toy function that replaces the content of a given string with "My name is
 * Titan, Open Titan". If the char buffer given is too small, it fills the
 * buffer as far as is possible.
 *
 * @param input The string to have it's content replaced.
 */
extern void get_name(char *input);

/**
 * A toy function that takes an ASCII string and converts every capital letter
 * into a lowercase letter.
 *
 * @param input The string to be converted to lowercase.
 */
extern void make_lower_case(char *input);

enum {
  // The memory address to which the functions will be mapped.
  kRemapAddress = 0xa0000000,
  // Alignment of the functions in asm.
  kRemapAlignment = 256,
};

static str_fn_t remapped_function = (str_fn_t)kRemapAddress;

// Short-hand arrays. (Allow slots and buses to be simply indexed.)
const dif_rv_core_ibex_addr_translation_bus_t kBuses[] = {
    kDifRvCoreIbexAddrTranslationIBus, kDifRvCoreIbexAddrTranslationDBus};
const dif_rv_core_ibex_addr_translation_slot_t kSlots[] = {
    kDifRvCoreIbexAddrTranslationSlot_0, kDifRvCoreIbexAddrTranslationSlot_1};

// Stores whether an access fault exception has fired.
static volatile bool access_fault = false;

/**
 * Overrides the default OTTF exception handler.
 *
 * This exception handler only processes the faults that are relevant to this
 * test. It falls into an infinite `wait_for_interrupt` routine (by calling
 * `abort()`) for the rest.
 *
 * The controlled fault originates in unmapped virtual memory. Normally the
 * return address would be calculated relative to the trapped instruction.
 * However, due to the virtual memory not being mapped to physical memory, this
 * approach would not work.
 *
 * Instead the control flow needs to be returned to the caller. In other words,
 * test_main -> unmapped vitual memory -> exception_handler -> test_main.
 *
 * Before the jump into the exception handler, the register set is saved on
 * stack by the OTTF exception handler entry subroutine, which means that the
 * return address can be loaded from there. See comments below for more details.
 */
void ottf_exception_handler(void) {
  // The frame address is the address of the stack location that holds the
  // `mepc`, since the OTTF exception handler entry code saves the `mepc` to
  // the top of the stack before transferring control flow to the exception
  // handler function (which is overridden here). See the `handler_exception`
  // subroutine in `sw/device/lib/testing/testing/ottf_isrs.S` for more details.
  uintptr_t mepc_stack_addr = (uintptr_t)OT_FRAME_ADDR();

  // The return address of the function that holds the trapping instruction is
  // the second top-most value placed on the stack by the OTTF exception handler
  // entry code. We grab this off the stack so that we can use it to overwrite
  // the `mepc` value stored on the stack, so that the `ottf_isr_exit`
  // subroutine (in `sw/device/lib/testing/test_framework/ottf_isrs.S`) will
  // restore control flow to the `test_main` function as described
  // above.
  uintptr_t ret_addr = *(uintptr_t *)(mepc_stack_addr + OTTF_WORD_SIZE);

  uint32_t mcause = ibex_mcause_read();
  ibex_exc_t exception = mcause & kIbexExcMax;

  switch (exception) {
    case kIbexExcInstrAccessFault:
      LOG_INFO("Instruction access fault handler");
      access_fault = true;
      *(uintptr_t *)mepc_stack_addr = ret_addr;
      break;
    default:
      LOG_FATAL("Unexpected exception id = 0x%x", exception);
      abort();
  }
}

/**
 * Configures the given address translation mapping in the given slot
 * for both IBus and DBus.
 *
 * @param ibex_core A handle to the ibex core.
 * @param slot The slot to be used for mapping.
 * @param mapping A description of the mapping.
 */
void map_to_slot(dif_rv_core_ibex_t *ibex_core,
                 dif_rv_core_ibex_addr_translation_slot_t slot,
                 dif_rv_core_ibex_addr_translation_mapping_t mapping) {
  for (size_t idx = 0; idx < 2; ++idx) {
    CHECK_DIF_OK(dif_rv_core_ibex_configure_addr_translation(
        ibex_core, slot, kBuses[idx], mapping));
  };
}

/**
 * Enables IBus and DBus address translation for the given slot.
 *
 * @param ibex_core A handle to the ibex core.
 * @param slot The slot to be used enabled.
 */
void enable_slot(dif_rv_core_ibex_t *ibex_core,
                 dif_rv_core_ibex_addr_translation_slot_t slot) {
  for (size_t idx = 0; idx < 2; ++idx) {
    CHECK_DIF_OK(
        dif_rv_core_ibex_enable_addr_translation(ibex_core, slot, kBuses[idx]));
  };
}

bool test_main(void) {
  // Unlock the entire address space for RWX so that we can run this test with
  // both rom and test_rom.
  CSR_WRITE(CSR_REG_PMPCFG3, (kEpmpModeNapot | kEpmpPermLockedReadWriteExecute)
                                 << 24);
  CSR_SET_BITS(CSR_REG_PMPADDR15, 0x7fffffff);
  CSR_WRITE(CSR_REG_PMPCFG2, 0);
  CSR_WRITE(CSR_REG_PMPCFG1, 0);
  CSR_WRITE(CSR_REG_PMPCFG0, 0);

  char test_str[] = TEST_STR;
  make_lower_case(test_str);
  CHECK_STR_EQ(test_str, EXPECTED_RESULT_MAKE_LOWER_CASE);

  get_name(test_str);
  CHECK_STR_EQ(test_str, EXPECTED_RESULT_GET_NAME);

  // Create translation descriptions.
  dif_rv_core_ibex_addr_translation_mapping_t make_lower_case_mapping = {
      .matching_addr = kRemapAddress,
      .remap_addr = (uintptr_t)make_lower_case,
      .size = kRemapAlignment,
  };
  dif_rv_core_ibex_addr_translation_mapping_t get_name_mapping = {
      .matching_addr = kRemapAddress,
      .remap_addr = (uintptr_t)get_name,
      .size = kRemapAlignment,
  };

  // Get ibex core handle.
  dif_rv_core_ibex_t ibex_core;
  CHECK_DIF_OK(dif_rv_core_ibex_init(
      mmio_region_from_addr(TOP_EARLGREY_RV_CORE_IBEX_CFG_BASE_ADDR),
      &ibex_core));

  // Map virtual address space to make_lower_case() using slot 1.
  map_to_slot(&ibex_core, kSlots[1], make_lower_case_mapping);

  // Enable address translation slot 1.
  enable_slot(&ibex_core, kSlots[1]);

  // Reset test string content.
  memcpy(test_str, TEST_STR, sizeof(test_str));

  // Run make_lower_case() from virtual memory and check the result.
  remapped_function(test_str);
  CHECK_STR_EQ(test_str, EXPECTED_RESULT_MAKE_LOWER_CASE);

  // Remap virtual address space to get_name() using slot 1.
  map_to_slot(&ibex_core, kSlots[1], get_name_mapping);

  // Run get_name() from virtual memory and check the result.
  remapped_function(test_str);
  CHECK_STR_EQ(test_str, EXPECTED_RESULT_GET_NAME);

  /////////////////////////////////////////////////////////////////////////////
  // Check slot 0 has higher priority than slot 1.
  /////////////////////////////////////////////////////////////////////////////
  //
  // Map virtual address space to make_lower_case() but using slot 0.
  map_to_slot(&ibex_core, kSlots[0], make_lower_case_mapping);

  // Enable address translation slot 0.
  enable_slot(&ibex_core, kSlots[0]);

  // Reset test string content.
  memcpy(test_str, TEST_STR, sizeof(test_str));

  // Run get_name() from virtual memory and check the result.
  remapped_function(test_str);
  CHECK_STR_EQ(test_str, EXPECTED_RESULT_MAKE_LOWER_CASE);

  /////////////////////////////////////////////////////////////////////////////
  // Check address translation no longer occurs after being disabled.
  /////////////////////////////////////////////////////////////////////////////
  //
  // Disable all address translation.
  for (size_t slot_i = 0; slot_i < 2; ++slot_i) {
    for (size_t bus_i = 0; bus_i < 2; ++bus_i) {
      CHECK_DIF_OK(dif_rv_core_ibex_disable_addr_translation(
          &ibex_core, kSlots[slot_i], kBuses[bus_i]));
    }
  }

  // Ensure there hasn't already been an access fault.
  CHECK(!access_fault);

  // Try to run the remap address as a function.
  remapped_function(test_str);

  // Ensure the exception has fired.
  CHECK(access_fault);

  return true;
}
