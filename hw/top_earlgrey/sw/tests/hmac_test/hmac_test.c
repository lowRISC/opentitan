// Copyright (c) 2022 ETH Zurich and University of Bologna
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.
//
//

#include "hw/top_earlgrey/sw/tests/common/utils.h"
#include <stdbool.h>
//#include "hw/top_earlgrey/sw/tests/hmac_test/hmac_api.c"

#define HYPER
#define IBEX
#define MBOX
#define ARIANE
#define TARGET_SYNTHESIS

#include "sw/device/lib/arch/device.h"
#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/dif/dif_hmac.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/hmac_testutils.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"


static const dif_hmac_transaction_t kHmacTransactionConfig = {
    .digest_endianness = kDifHmacEndiannessLittle,
    .message_endianness = kDifHmacEndiannessLittle,
};

static const char kData[142] =
    "Every one suspects himself of at least one of "
    "the cardinal virtues, and this is mine: I am "
    "one of the few honest people that I have ever "
    "known";

static uint32_t kHmacKey[8] = {
    0xec4e6c89, 0x082efa98, 0x299f31d0, 0xa4093822,
    0x03707344, 0x13198a2e, 0x85a308d3, 0x243f6a88,
};

static const dif_hmac_digest_t kExpectedShaDigest = {
    .digest =
        {
            0xd6c6c94e,
            0xf7cff519,
            0x45c76d42,
            0x9d37a8b8,
            0xe2762fe9,
            0x71ff68cb,
            0x68e236af,
            0x3dc296dc,
        },
};

static const dif_hmac_digest_t kExpectedHmacDigest = {
    .digest =
        {
            0xebce4019,
            0x284d39f1,
            0x5eae12b0,
            0x0c48fb23,
            0xfadb9531,
            0xafbbf3c2,
            0x90d3833f,
            0x397b98e4,
        },
};

/**
 * Initialize the HMAC engine. Return `true` if the configuration is valid.
 */
static void test_setup(mmio_region_t base_addr, dif_hmac_t *hmac) {
  CHECK_DIF_OK(dif_hmac_init(base_addr, hmac));
}

/**
 * Start HMAC in the correct mode. If `key` == NULL use SHA256 mode, otherwise
 * use the provided key in HMAC mode.
 */
static void test_start(const dif_hmac_t *hmac, const uint8_t *key) {
  // Let a null key indicate we are operating in SHA256-only mode.
  if (key == NULL) {
    CHECK_DIF_OK(dif_hmac_mode_sha256_start(hmac, kHmacTransactionConfig));
  } else {
    CHECK_DIF_OK(dif_hmac_mode_hmac_start(hmac, key, kHmacTransactionConfig));
  }
}

/**
 * Kick off the HMAC (or SHA256) run.
 */
static void run_hmac(const dif_hmac_t *hmac) {
  CHECK_DIF_OK(dif_hmac_process(hmac));
}

static void run_test(const dif_hmac_t *hmac, const char *data, size_t len,
                     const uint8_t *key,
                     const dif_hmac_digest_t *expected_digest) {
  test_start(hmac, key);
  hmac_testutils_push_message(hmac, data, len);
   hmac_testutils_fifo_empty_polled(hmac);
  hmac_testutils_check_message_length(hmac, len * 8);
  run_hmac(hmac);
  hmac_testutils_finish_and_check_polled(hmac, expected_digest);
}

bool test_main(void) {
  printf("Running HMAC DIF test...\r\n");

  dif_hmac_t hmac;
  test_setup(mmio_region_from_addr(TOP_EARLGREY_HMAC_BASE_ADDR), &hmac);

  printf("Running test SHA256 pass 1...\r\n");
  run_test(&hmac, kData, sizeof(kData), NULL, &kExpectedShaDigest);

  printf("Running test SHA256 pass 2...\r\n");
  run_test(&hmac, kData, sizeof(kData), NULL, &kExpectedShaDigest);

  printf("Running test HMAC pass 1...\r\n");
  run_test(&hmac, kData, sizeof(kData), (uint8_t *)(&kHmacKey[0]),
           &kExpectedHmacDigest);

  printf("Running test HMAC pass 2...\r\n");
  run_test(&hmac, kData, sizeof(kData), (uint8_t *)(&kHmacKey[0]),
           &kExpectedHmacDigest);

  return true;
}

int main(int argc, char **argv) {

  bool t;
  
  // UART setup
  #ifdef TARGET_SYNTHESIS                
  int baud_rate = 115200;
  int test_freq = 40000000;
  #else
  int baud_rate = 115200;
  int test_freq = 100000000;
  #endif
  uart_set_cfg(0,(test_freq/baud_rate)>>4);
  /*
  // move interrupt vector to SRAM base address
  unsigned val = 0xe0000001;                      
  asm volatile("csrw mtvec, %0\n" : : "r"(val));

  printf("Initializing entropy src and HMAC\r\n");
  t = entropy_init();    // init the entropy source
  
  printf("Writing the crypto key to the HMAC\r\n");
  t = hmac_write_key();  // dummy key
  t = hmac_init();       // write the control register

  printf("Preloading MBOX, Ibex SRAM, Ariane SRAM, HyperRam\r\n");
  t = preload_mbox();
  t = preload_ariane();
  t = preload_ibex();
  t = preload_hyper();
   
  printf("Moving data from Mbox to HMAC\r\n");
  t = hmac_init(); 
  t = hmac_input_mbox();

  printf("Encrypt!\r\n");
  t = hmac_encrypt();
  t = hmac_read_out();

  printf("Moving data from Ariane SRAM to HMAC\r\n");
  t = hmac_init(); 
  t = hmac_input_ariane();
  
  printf("Encrypt!\r\n");
  t = hmac_encrypt();
  t = hmac_read_out();
  
  printf("Moving data from Ibex SRAM to HMAC\r\n");
  t = hmac_init(); 
  t = hmac_input_ibex();

  printf("Encrypt!\r\n");
  t = hmac_encrypt();
  t = hmac_read_out();

  printf("Moving data from HyperRAM to HMAC\r\n");
  t = hmac_init(); 
  t = hmac_input_hyper();
  
  printf("Encrypt!\r\n");
  t = hmac_encrypt();
  t = hmac_read_out();

  //printf("Test succeed\r\n");
  */
  t = test_main();
  return 0;
}
