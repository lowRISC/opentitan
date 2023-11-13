// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/base/status.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/json/command.h"
#include "sw/device/lib/testing/json/mem.h"
#include "sw/device/lib/testing/test_framework/check.h"
//#include "sw/device/lib/testing/test_framework/ottf_main.h"
#include "sw/device/lib/testing/test_framework/ottf_test_config.h"
#include "sw/device/lib/runtime/ibex.h"

#include "sw/device/lib/testing/test_framework/ujson_ottf.h"
#include "sw/device/lib/testing/test_framework/ujson_ottf_commands.h"
#include "sw/device/lib/ujson/ujson.h"

#include "sw/device/lib/arch/device.h"
#include "sw/device/lib/dif/dif_uart.h"
#include "sw/device/lib/runtime/print.h"
#include "sw/device/lib/testing/pinmux_testutils.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

OTTF_DEFINE_TEST_CONFIG(.enable_uart_flow_control = true);

volatile uint32_t kTestWord;
volatile uint32_t kEndTest;

static dif_uart_t uart;
static dif_pinmux_t pinmux;


status_t command_processor(ujson_t *uj) {
  while (!kEndTest) {
    test_command_t command;
    TRY(ujson_deserialize_test_command_t(uj, &command));
    status_t status = ujson_ottf_dispatch(uj, command);
    if (status_err(status) == kUnimplemented) {
      RESP_ERR(uj, status);
    } else if (status_err(status) != kOk) {
      return status;
    }
  }
  return OK_STATUS();
}
#define EXECUTE_TEST(result_, test_function_, ...)                       \
  do {                                                                   \
    LOG_INFO("Starting test " #test_function_ "...");                    \
    uint64_t t_start_ = ibex_mcycle_read();                              \
    status_t local_status = INTO_STATUS(test_function_(__VA_ARGS__));    \
    uint64_t cycles_ = ibex_mcycle_read() - t_start_;                    \
    CHECK(kClockFreqCpuHz <= UINT32_MAX, "");                            \
    uint32_t clock_mhz = (uint32_t)kClockFreqCpuHz / 1000000;            \
    if (status_ok(local_status)) {                                       \
      if (cycles_ <= UINT32_MAX) {                                       \
        uint32_t micros = (uint32_t)cycles_ / clock_mhz;                 \
        LOG_INFO("Successfully finished test " #test_function_           \
                 " in %u cycles or %u us @ %u MHz.",                     \
                 (uint32_t)cycles_, micros, clock_mhz);                  \
      } else {                                                           \
        uint32_t cycles_lower_ = (uint32_t)(cycles_ & UINT32_MAX);       \
        uint32_t cycles_upper_ = (uint32_t)(cycles_ >> 32);              \
        LOG_INFO("Successfully finished test " #test_function_           \
                 " in 0x%08x%08x cycles.",                               \
                 cycles_upper_, cycles_lower_);                          \
      }                                                                  \
    } else {                                                             \
      result_ = local_status;                                            \
      LOG_ERROR("Finished test " #test_function_ ": %r.", local_status); \
    }                                                                    \
  } while (0)

bool sram_main(void) {
  // Initialize UART console.
  CHECK_DIF_OK(dif_pinmux_init(
      mmio_region_from_addr(TOP_EARLGREY_PINMUX_AON_BASE_ADDR), &pinmux));
  CHECK_DIF_OK(dif_uart_init(
      mmio_region_from_addr(TOP_EARLGREY_UART0_BASE_ADDR), &uart));
  pinmux_testutils_init(&pinmux);
  CHECK(kUartBaudrate <= UINT32_MAX, "kUartBaudrate must fit in uint32_t");
  CHECK(kClockFreqPeripheralHz <= UINT32_MAX,
        "kClockFreqPeripheralHz must fit in uint32_t");
  CHECK_DIF_OK(dif_uart_configure(
      &uart, (dif_uart_config_t){
                 .baudrate = (uint32_t)kUartBaudrate,
                 .clk_freq_hz = (uint32_t)kClockFreqPeripheralHz,
                 .parity_enable = kDifToggleDisabled,
                 .parity = kDifUartParityEven,
                 .tx_enable = kDifToggleEnabled,
                 .rx_enable = kDifToggleEnabled,
             }));
  base_uart_stdout(&uart);

  kEndTest = 0;
  kTestWord = 0xface1234u;
  LOG_INFO("otdbg:before:kTestWord: %d",kTestWord);

  ujson_t uj = ujson_ottf_console();

  status_t result = OK_STATUS();
  EXECUTE_TEST(result, command_processor, &uj);

  LOG_INFO("otdbg:after:kTestWord: %d",kTestWord);

  return status_ok(result);
}
