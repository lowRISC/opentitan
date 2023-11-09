// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/arch/device.h"
#include "sw/device/lib/base/csr.h"
#include "sw/device/lib/dif/dif_uart.h"
#include "sw/device/lib/runtime/ibex.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/runtime/pmp.h"
#include "sw/device/lib/runtime/print.h"
#include "sw/device/lib/testing/pinmux_testutils.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_test_config.h"
#include "sw/device/lib/testing/test_framework/status.h"
#include "sw/device/silicon_creator/lib/dbg_print.h"
#include "sw/device/silicon_creator/lib/epmp_defs.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

OTTF_DEFINE_TEST_CONFIG();

/**
 * Labels
 */
// The end of the rodata region.
// This is set in the linker script.
extern const char __rodata_end[];
// The start and the end of the user's test function.
extern const char i_am_become_user[];
extern const char kIAmBecomeUserEnd[];
// Expected U Mode Instruction Access Fault Return Address
extern const char kExpUInstrAccFaultRet[];
// Expected M Mode Instruction Access Fault Return Address
extern const char kExpMInstrAccFaultRet[];

extern void (*finish_test)(void);

/**
 * Diff handles
 */
static dif_uart_t uart0;
static dif_pinmux_t pinmux;

/**
 * The location in memory which will be used to test permissions.
 *
 * They are set up by `pmp_setup_test_locations` as such:
 *
 * | Location | L | R | W | X | U Mode | M Mode |
 * |----------|---|---|---|---|--------|--------|
 * |     0    | 0 | 1 | 0 | 0 |  R     |        |
 * |     1    | 1 | 1 | 1 | 0 |        |  RW    |
 * |     2    | 0 | 0 | 1 | 0 |  R     |  RW    |
 * |     3    | 1 | 0 | 1 | 1 |    X   |  R X   |
 *
 * Note: mseccfg.MML is set in this test,
 * so permissions differ from standard (non-MML) PMP.
 */
enum { kNumLocations = 4 };
volatile uint32_t test_locations[kNumLocations] = {
    // Random Numbers
    [0] = 0x3779cdc5,
    [1] = 0x76bce080,
    [2] = 0xae8a4ed7,
    // The `ret` instruction. (This region is executable.)
    [3] = 0x00008067,
};

static inline bool was_in_machine_mode(void) {
  uint32_t mstatus;
  CSR_READ(CSR_REG_MSTATUS, &mstatus);
  // If both MPP bits are set, then I was in machine mode.
  const uint32_t kMppOffset = 11;
  return ((mstatus >> kMppOffset) & 0x3) == 0x3;
}

void ottf_exception_handler(void) {
  uint32_t mtval = ibex_mtval_read();
  ibex_exc_t mcause = ibex_mcause_read();
  bool m_mode_exception = was_in_machine_mode();

  // The frame address is the address of the stack location that holds the
  // `mepc`, since the OTTF exception handler entry code saves the `mepc` to
  // the top of the stack before transferring control flow to the exception
  // handler function (which is overridden here). See the `handler_exception`
  // subroutine in `sw/device/lib/testing/testing/ottf_isrs.S` for more details.
  uintptr_t *mepc_stack_addr = (uintptr_t *)OT_FRAME_ADDR();
  uint32_t mpec = *mepc_stack_addr;

  switch (mcause) {
    case kIbexExcLoadAccessFault:
      if (m_mode_exception) {
        CHECK(mtval == (uint32_t)(test_locations + 0),
              "Unexpected M Mode Load Access Fault:"
              " mpec = 0x%08x, mtval = 0x%08x",
              mpec, mtval);
      } else {
        CHECK(mtval == (uint32_t)(test_locations + 1) ||
                  mtval == (uint32_t)(test_locations + 3),
              "Unexpected U Mode Load Access Fault:"
              " mpec = 0x%08x, mtval = 0x%08x",
              mpec, mtval);
      };
      break;
    case kIbexExcStoreAccessFault:
      if (m_mode_exception) {
        CHECK(mtval == (uint32_t)(test_locations + 0) ||
                  mtval == (uint32_t)(test_locations + 3),
              "Unexpected M Mode Store Access Fault:"
              " mpec = 0x%08x, mtval = 0x%08x",
              mpec, mtval);
      } else {
        CHECK(mtval == (uint32_t)(test_locations + 0) ||
                  mtval == (uint32_t)(test_locations + 1) ||
                  mtval == (uint32_t)(test_locations + 2) ||
                  mtval == (uint32_t)(test_locations + 3),
              "Unexpected U Mode Store Access Fault:"
              " mpec = 0x%08x, mtval = 0x%08x",
              mpec, mtval);
      };
      break;
    case kIbexExcInstrAccessFault:
      CHECK(mtval == (uint32_t)(test_locations + 0) ||
                mtval == (uint32_t)(test_locations + 1) ||
                mtval == (uint32_t)(test_locations + 2),
            "Unexpected Instruction Access Fault:"
            " mpec = 0x%08x, mtval = 0x%08x",
            mpec, mtval);
      *mepc_stack_addr = m_mode_exception ? (uintptr_t)kExpMInstrAccFaultRet
                                          : (uintptr_t)kExpUInstrAccFaultRet;
      break;
    case kIbexExcUserECall:
      test_status_set(kTestStatusPassed);
      finish_test();
      OT_UNREACHABLE();
    default:
      CHECK(false,
            "Unexpected Exception:"
            " mcause = 0x%x, mpec 0x%x, mtval = 0x%x",
            mcause, mpec, mtval);
      OT_UNREACHABLE();
  }
}

/**
 * Converts an address to a TOR address field value.
 *
 * @param addr The address to convert.
 * @return The given address encoded as a TOR address field value.
 */
inline uint32_t tor_address(uint32_t addr) { return addr >> 2; }

/**
 * Finds the pmpcfg CSR for a given PMP region.
 *
 * @param region PMP region.
 * @return The address of the pmpcfg CSR of the given region.
 */
inline uint32_t region_pmpcfg(uint32_t region) {
  switch (region / 4) {
    case 0:
      return CSR_REG_PMPCFG0;
    case 1:
      return CSR_REG_PMPCFG1;
    case 2:
      return CSR_REG_PMPCFG2;
    case 3:
      return CSR_REG_PMPCFG3;
    default:
      OT_UNREACHABLE();
  };
}

/**
 * Finds offset of a region's configuration in it's pmpcfg CSR.
 *
 * @param region PMP region.
 * @return pmpcfg offset.
 */
inline uint32_t region_offset(uint32_t region) { return region % 4 * 8; }

/**
 * Sets up the execution area of Machine Mode.
 *
 * This configuration adjusts the existing configuration from the
 * [reset PMP configuration](/hw/ip/rv_core_ibex/rtl/ibex_pmp_reset.svh)
 * and [SRAM loader](/sw/host/opentitanlib/src/test_utils/load_sram_program.rs).
 *
 * These changes are needed before mseccfg.MML is enabled,
 * because LRWX permissions become read only for machine mode.
 */
static void pmp_setup_machine_area(void) {
  // Set up the writeable section of the SRAM executable.
  //
  // Note: this overlaps a region covering the whole of SRAM (region 15),
  // but is in a lower PMP register so region 15's configuration
  // will be ignored in this area.
  const uint32_t kRodataEnd = (uint32_t)__rodata_end;
  const uint32_t kSramEnd = TOP_EARLGREY_SRAM_CTRL_MAIN_RAM_BASE_ADDR +
                            TOP_EARLGREY_SRAM_CTRL_MAIN_RAM_SIZE_BYTES;

  CSR_WRITE(CSR_REG_PMPADDR8, tor_address(kRodataEnd));
  CSR_WRITE(CSR_REG_PMPADDR9, tor_address(kSramEnd));

  const uint32_t pmp9cfg = EPMP_CFG_A_TOR | EPMP_CFG_LRW;
  CSR_SET_BITS(region_pmpcfg(9), pmp9cfg << region_offset(1));

  // Clear the execution permissions on region 11 (MMIO)
  CSR_CLEAR_BITS(region_pmpcfg(11), EPMP_CFG_X << region_offset(11));
  uint32_t csr;
  CSR_READ(region_pmpcfg(11), &csr);
  CHECK(!((csr >> region_offset(11)) & EPMP_CFG_X),
        "Couldn't remove execute access to PMP region 11.");

  // Clear the write permissions on regions 13 (DV ROM) and 15 (all SRAM)
  CSR_CLEAR_BITS(region_pmpcfg(13), EPMP_CFG_W << region_offset(13));
  CSR_CLEAR_BITS(region_pmpcfg(15), EPMP_CFG_W << region_offset(15));
  CSR_READ(region_pmpcfg(13), &csr);
  CHECK(!((csr >> region_offset(13)) & EPMP_CFG_W),
        "Couldn't remove write access from PMP region 15.");
  CHECK(!((csr >> region_offset(15)) & EPMP_CFG_W),
        "Couldn't remove write access from PMP region 15.");
}

/**
 * Sets up the User Mode test function to be executable in user mode.
 *
 * *It wouldn't be very useful if it wasn't.*
 */
static void pmp_setup_user_area(void) {
  const uintptr_t kStart = (uintptr_t)i_am_become_user;
  const uintptr_t kEnd = (uintptr_t)kIAmBecomeUserEnd;

  CSR_WRITE(CSR_REG_PMPADDR0, tor_address(kStart));
  CSR_WRITE(CSR_REG_PMPADDR1, tor_address(kEnd));

  const uint32_t pmp1cfg = (EPMP_CFG_A_TOR | EPMP_CFG_LRWX) ^ EPMP_CFG_R;
  CSR_SET_BITS(region_pmpcfg(1), pmp1cfg << region_offset(1));
}

/**
 * Sets up the permissions for the test locations.
 *
 * See the declaration of `test_locations`
 * to see the desired permission settings.
 */
static void pmp_setup_test_locations(void) {
  CSR_WRITE(CSR_REG_PMPADDR3, tor_address((uintptr_t)(test_locations + 0)));
  CSR_WRITE(CSR_REG_PMPADDR4, tor_address((uintptr_t)(test_locations + 1)));
  CSR_WRITE(CSR_REG_PMPADDR5, tor_address((uintptr_t)(test_locations + 2)));
  CSR_WRITE(CSR_REG_PMPADDR6, tor_address((uintptr_t)(test_locations + 3)));
  CSR_WRITE(CSR_REG_PMPADDR7, tor_address((uintptr_t)(test_locations + 4)));

  uint32_t cfg = EPMP_CFG_A_TOR | EPMP_CFG_R;
  CSR_SET_BITS(region_pmpcfg(4), cfg << region_offset(4));
  cfg = EPMP_CFG_A_TOR | EPMP_CFG_LRW;
  CSR_SET_BITS(region_pmpcfg(5), cfg << region_offset(5));
  cfg = EPMP_CFG_A_TOR | EPMP_CFG_W;
  CSR_SET_BITS(region_pmpcfg(6), cfg << region_offset(6));
  cfg = EPMP_CFG_A_TOR | EPMP_CFG_L | EPMP_CFG_X | EPMP_CFG_W;
  CSR_SET_BITS(region_pmpcfg(7), cfg << region_offset(7));
}

/**
 * Sets up the UART connection.
 */
static void setup_uart(void) {
  // Initialise DIF handles
  CHECK_DIF_OK(dif_pinmux_init(
      mmio_region_from_addr(TOP_EARLGREY_PINMUX_AON_BASE_ADDR), &pinmux));
  CHECK_DIF_OK(dif_uart_init(
      mmio_region_from_addr(TOP_EARLGREY_UART0_BASE_ADDR), &uart0));

  // Initialise UART console.
  pinmux_testutils_init(&pinmux);
  CHECK(kUartBaudrate <= UINT32_MAX, "kUartBaudrate must fit in uint32_t");
  CHECK(kClockFreqPeripheralHz <= UINT32_MAX,
        "kClockFreqPeripheralHz must fit in uint32_t");
  CHECK_DIF_OK(dif_uart_configure(
      &uart0, (dif_uart_config_t){
                  .baudrate = (uint32_t)kUartBaudrate,
                  .clk_freq_hz = (uint32_t)kClockFreqPeripheralHz,
                  .parity_enable = kDifToggleDisabled,
                  .parity = kDifUartParityEven,
                  .tx_enable = kDifToggleEnabled,
                  .rx_enable = kDifToggleEnabled,
              }));
  base_uart_stdout(&uart0);
}

/**
 * The entry point of the SRAM program.
 *
 * *Control flow passed from `sram_start`.*
 */
void sram_main(void) {
  setup_uart();

  // Must set up the Machine Mode Area Correctly
  // before entering Machine Mode Lockdown.
  pmp_setup_machine_area();

  LOG_INFO("Enable Machine Mode Lockdown");
  CSR_SET_BITS(CSR_REG_MSECCFG, EPMP_MSECCFG_MML);

  pmp_setup_user_area();
  pmp_setup_test_locations();

  LOG_INFO("The PMP Config:");
  dbg_print_epmp();

  LOG_INFO("Machine Mode Tests");
  uint32_t load;
  for (size_t loc = 0; loc < kNumLocations; ++loc) {
    test_locations[loc] = 42;
    load = test_locations[loc];
    ((void (*)(void))(test_locations + loc))();
    // The address to return to after an expected
    // instruction access fault has occurred.
    OT_ADDRESSABLE_LABEL(kExpMInstrAccFaultRet);
  };
  // Pretending to use load
  (void)load;

  LOG_INFO("User Mode Tests");
  // Jump to the user area to perform user tests.
  asm volatile(
      "la t0, i_am_become_user\n"
      "csrw mepc, t0\n"
      "mret\n"
      :  // The clobber doesn't really matter;
      :  // we're not comming back.
      : "t0");
  OT_UNREACHABLE();
}
