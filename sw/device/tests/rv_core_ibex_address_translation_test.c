// Copyright lowRISC contributors (OpenTitan project).
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
#include "sw/device/silicon_creator/lib/epmp_state.h"

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

/**
 * Function that will be mapped to. Produces illegal instruction exception if
 * unmapped.
 */
extern void remapped_function(char *input);

enum {
  // Alignment of the functions in asm.
  kRemapAlignment = 256,
};

// Short-hand arrays. (Allow slots to be simply indexed.)
const dif_rv_core_ibex_addr_translation_slot_t kSlots[] = {
    kDifRvCoreIbexAddrTranslationSlot_0, kDifRvCoreIbexAddrTranslationSlot_1};

// Translation descriptions to use.
// Junk bits (0xDEADBEEF) are added to the `remap_addr` fields to ensure they
// are ignored by the translation mechanism.
static const dif_rv_core_ibex_addr_translation_mapping_t kMakeLowerCaseMapping =
    {
        .matching_addr = (uintptr_t)remapped_function,
        .remap_addr = (uintptr_t)make_lower_case +
                      (uintptr_t)(0xDEADBEEF & (kRemapAlignment - 1)),
        .size = kRemapAlignment,
};
static const dif_rv_core_ibex_addr_translation_mapping_t kGetNameMapping = {
    .matching_addr = (uintptr_t)remapped_function,
    .remap_addr =
        (uintptr_t)get_name + (uintptr_t)(0xDEADBEEF & (kRemapAlignment - 1)),
    .size = kRemapAlignment,
};

// Stores whether an access fault exception has fired.
static volatile bool illegal_instr_fault = false;

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
void ottf_exception_handler(uint32_t *exc_info) {
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
    case kIbexExcIllegalInstrFault:
      LOG_INFO("Illegal instruction fault handler");
      illegal_instr_fault = true;
      *(uintptr_t *)mepc_stack_addr = ret_addr;
      break;
    default:
      LOG_FATAL("Unexpected exception id = 0x%x", exception);
      CHECK(false);
  }
}

/**
 * Configures the given address translation mapping in the given slot and bus.
 *
 * @param ibex_core A handle to the ibex core.
 * @param slot The slot index to be used for mapping.
 * @param bus The bus to be used for mapping.
 * @param mapping A description of the mapping.
 */
void map_to_slot(dif_rv_core_ibex_t *ibex_core, size_t slot,
                 dif_rv_core_ibex_addr_translation_bus_t bus,
                 dif_rv_core_ibex_addr_translation_mapping_t mapping) {
  CHECK_DIF_OK(dif_rv_core_ibex_configure_addr_translation(
      ibex_core, kSlots[slot], bus, mapping));
}

/**
 * Enables address translation for the given slot and bus.
 *
 * @param ibex_core A handle to the ibex core.
 * @param slot The slot index to be used enabled.
 * @param bus The bus to be enabled.
 */
void enable_slot(dif_rv_core_ibex_t *ibex_core, size_t slot,
                 dif_rv_core_ibex_addr_translation_bus_t bus) {
  CHECK_DIF_OK(
      dif_rv_core_ibex_enable_addr_translation(ibex_core, kSlots[slot], bus));
}

/**
 * Disables address translation for the given slot and bus.
 *
 * @param ibex_core A handle to the ibex core.
 * @param slot The slot index to be used enabled.
 * @param bus The bus to be enabled.
 */
void disable_slot(dif_rv_core_ibex_t *ibex_core, size_t slot,
                  dif_rv_core_ibex_addr_translation_bus_t bus) {
  CHECK_DIF_OK(
      dif_rv_core_ibex_disable_addr_translation(ibex_core, kSlots[slot], bus));
}

void check_ibus_map(dif_rv_core_ibex_t *ibex_core) {
  // Check the functions are expected before doing the mapping test.
  char test_str[] = TEST_STR;
  make_lower_case(test_str);
  CHECK_STR_EQ(test_str, EXPECTED_RESULT_MAKE_LOWER_CASE);

  get_name(test_str);
  CHECK_STR_EQ(test_str, EXPECTED_RESULT_GET_NAME);

  // Map virtual address space to make_lower_case() using slot 1.
  map_to_slot(ibex_core, 1, kDifRvCoreIbexAddrTranslationIBus,
              kMakeLowerCaseMapping);

  // Enable address translation slot 1.
  enable_slot(ibex_core, 1, kDifRvCoreIbexAddrTranslationIBus);

  // Reset test string content.
  memcpy(test_str, TEST_STR, sizeof(test_str));

  // Run make_lower_case() from virtual memory and check the result.
  remapped_function(test_str);
  CHECK_STR_EQ(test_str, EXPECTED_RESULT_MAKE_LOWER_CASE);

  // Remap virtual address space to get_name() using slot 1.
  map_to_slot(ibex_core, 1, kDifRvCoreIbexAddrTranslationIBus, kGetNameMapping);

  // Run get_name() from virtual memory and check the result.
  remapped_function(test_str);
  CHECK_STR_EQ(test_str, EXPECTED_RESULT_GET_NAME);

  /////////////////////////////////////////////////////////////////////////////
  // Check slot 0 has higher priority than slot 1.
  /////////////////////////////////////////////////////////////////////////////
  //
  // Map virtual address space to make_lower_case() but using slot 0.
  map_to_slot(ibex_core, 0, kDifRvCoreIbexAddrTranslationIBus,
              kMakeLowerCaseMapping);

  // Enable address translation slot 0.
  enable_slot(ibex_core, 0, kDifRvCoreIbexAddrTranslationIBus);

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
    disable_slot(ibex_core, slot_i, kDifRvCoreIbexAddrTranslationIBus);
  }

  // Ensure there hasn't already been an access fault.
  CHECK(!illegal_instr_fault);

  // Try to run the remap address as a function.
  remapped_function(test_str);

  // Ensure the exception has fired.
  CHECK(illegal_instr_fault);
}

void check_dbus_map(dif_rv_core_ibex_t *ibex_core) {
  CHECK_ARRAYS_NE((uint8_t *)make_lower_case, (uint8_t *)get_name,
                  kRemapAlignment,
                  "make_lower_case and get_name are the same!");
  CHECK_ARRAYS_NE((uint8_t *)make_lower_case, (uint8_t *)remapped_function,
                  kRemapAlignment,
                  "make_lower_case and remapped_function are the same!");
  CHECK_ARRAYS_NE((uint8_t *)get_name, (uint8_t *)remapped_function,
                  kRemapAlignment,
                  "get_name and remapped_function are the same!");

  // Map virtual address space to make_lower_case() using slot 1.
  map_to_slot(ibex_core, 1, kDifRvCoreIbexAddrTranslationDBus,
              kMakeLowerCaseMapping);

  // Enable address translation slot 1.
  enable_slot(ibex_core, 1, kDifRvCoreIbexAddrTranslationDBus);

  CHECK_ARRAYS_EQ((uint8_t *)make_lower_case, (uint8_t *)remapped_function,
                  kRemapAlignment,
                  "remapped_function is not mapped to make_lower_case!");

  // Remap virtual address space to get_name() using slot 1.
  map_to_slot(ibex_core, 1, kDifRvCoreIbexAddrTranslationDBus, kGetNameMapping);

  CHECK_ARRAYS_EQ((uint8_t *)get_name, (uint8_t *)remapped_function,
                  kRemapAlignment,
                  "remapped_function is not mapped to get_name!");

  /////////////////////////////////////////////////////////////////////////////
  // Check slot 0 has higher priority than slot 1.
  /////////////////////////////////////////////////////////////////////////////
  //
  // Map virtual address space to make_lower_case() but using slot 0.
  map_to_slot(ibex_core, 0, kDifRvCoreIbexAddrTranslationDBus,
              kMakeLowerCaseMapping);

  // Enable address translation slot 0.
  enable_slot(ibex_core, 0, kDifRvCoreIbexAddrTranslationDBus);

  CHECK_ARRAYS_EQ((uint8_t *)make_lower_case, (uint8_t *)remapped_function,
                  kRemapAlignment,
                  "remapped_function is not mapped to make_lower_case!");

  /////////////////////////////////////////////////////////////////////////////
  // Check address translation no longer occurs after being disabled.
  /////////////////////////////////////////////////////////////////////////////
  //
  // Disable all address translation.
  for (size_t slot_i = 0; slot_i < 2; ++slot_i) {
    disable_slot(ibex_core, slot_i, kDifRvCoreIbexAddrTranslationDBus);
  }

  CHECK_ARRAYS_NE((uint8_t *)make_lower_case, (uint8_t *)remapped_function,
                  kRemapAlignment,
                  "make_lower_case and remapped_function are the same!");
  CHECK_ARRAYS_NE((uint8_t *)get_name, (uint8_t *)remapped_function,
                  kRemapAlignment,
                  "make_lower_case and remapped_function are the same!");
}

bool test_main(void) {
  // Get ibex core handle.
  dif_rv_core_ibex_t ibex_core;
  CHECK_DIF_OK(dif_rv_core_ibex_init(
      mmio_region_from_addr(TOP_EARLGREY_RV_CORE_IBEX_CFG_BASE_ADDR),
      &ibex_core));

  check_ibus_map(&ibex_core);
  check_dbus_map(&ibex_core);

  return true;
}
