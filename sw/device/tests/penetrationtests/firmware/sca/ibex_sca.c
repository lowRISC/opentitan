// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/tests/penetrationtests/firmware/sca/ibex_sca.h"

#include "sw/device/lib/base/memory.h"
#include "sw/device/lib/base/status.h"
#include "sw/device/lib/dif/dif_keymgr.h"
#include "sw/device/lib/dif/dif_kmac.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/keymgr_testutils.h"
#include "sw/device/lib/testing/test_framework/ottf_test_config.h"
#include "sw/device/lib/testing/test_framework/ujson_ottf.h"
#include "sw/device/lib/ujson/ujson.h"
#include "sw/device/sca/lib/sca.h"
#include "sw/device/tests/penetrationtests/firmware/lib/sca_lib.h"
#include "sw/device/tests/penetrationtests/json/ibex_sca_commands.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

static dif_keymgr_t keymgr;
static dif_kmac_t kmac;

// Buffer to allow the compiler to allocate a safe area in Main SRAM where
// we can do the write/read test without the risk of clobbering data
// used by the program.
OT_SECTION(".data")
static volatile uint32_t sram_main_buffer[8];

status_t handle_ibex_sca_key_sideloading(ujson_t *uj) {
  ibex_sca_salt_t uj_data;
  TRY(ujson_deserialize_ibex_sca_salt_t(uj, &uj_data));

  // Initialize keymgr and advance to CreatorRootKey state.
  TRY(keymgr_testutils_startup(&keymgr, &kmac));

  // Generate identity at CreatorRootKey (to follow same sequence and reuse
  // chip_sw_keymgr_key_derivation_vseq.sv).
  TRY(keymgr_testutils_generate_identity(&keymgr));

  // Advance to OwnerIntermediateKey state.
  TRY(keymgr_testutils_advance_state(&keymgr, &kOwnerIntParams));
  TRY(keymgr_testutils_check_state(&keymgr,
                                   kDifKeymgrStateOwnerIntermediateKey));

  // Set the salt based on the input.
  dif_keymgr_versioned_key_params_t sideload_params = kKeyVersionedParams;
  for (int i = 0; i < 8; i++) {
    sideload_params.salt[i] = uj_data.salt[i];
  }

  // Trigger keymanager to create a new key based on the provided salt.
  sca_set_trigger_high();
  TRY(keymgr_testutils_generate_versioned_key(&keymgr, sideload_params));
  sca_set_trigger_low();

  // Read back generated key provided at the software interface.
  dif_keymgr_output_t key;
  TRY(dif_keymgr_read_output(&keymgr, &key));

  // Acknowledge test.
  ibex_sca_key_t uj_key;
  for (int i = 0; i < 8; i++) {
    uj_key.share0[i] = key.value[0][i];
    uj_key.share1[i] = key.value[1][i];
  }
  RESP_OK(ujson_serialize_ibex_sca_key_t, uj, &uj_key);
  return OK_STATUS();
}

status_t handle_ibex_sca_tl_write(ujson_t *uj) {
  // Get data to write into SRAM.
  ibex_sca_test_data_t uj_data;
  TRY(ujson_deserialize_ibex_sca_test_data_t(uj, &uj_data));

  // Get address of buffer located in SRAM.
  uintptr_t sram_main_buffer_addr = (uintptr_t)&sram_main_buffer;
  mmio_region_t sram_region_main_addr =
      mmio_region_from_addr(sram_main_buffer_addr);

  // SCA code target.
  for (int it = 0; it < uj_data.num_iterations; it++) {
    sca_set_trigger_high();
    // Write provided data into SRAM.
    for (int i = 0; i < 8; i++) {
      mmio_region_write32(sram_region_main_addr,
                          i * (ptrdiff_t)sizeof(uint32_t), uj_data.data[i]);
    }
    sca_set_trigger_low();
  }

  // Acknowledge test.
  ibex_sca_result_t uj_output;
  uj_output.result = 0;
  RESP_OK(ujson_serialize_ibex_sca_result_t, uj, &uj_output);
  return OK_STATUS();
}

status_t handle_ibex_sca_tl_read(ujson_t *uj) {
  // Get data to write into SRAM.
  ibex_sca_test_data_t uj_data;
  TRY(ujson_deserialize_ibex_sca_test_data_t(uj, &uj_data));

  // Get address of buffer located in SRAM.
  uintptr_t sram_main_buffer_addr = (uintptr_t)&sram_main_buffer;
  mmio_region_t sram_region_main_addr =
      mmio_region_from_addr(sram_main_buffer_addr);

  // Write provided data into SRAM.
  for (int i = 0; i < 8; i++) {
    mmio_region_write32(sram_region_main_addr, i * (ptrdiff_t)sizeof(uint32_t),
                        uj_data.data[i]);
  }

  uint32_t read_data[8];

  // SCA code target.
  for (int it = 0; it < uj_data.num_iterations; it++) {
    sca_set_trigger_high();
    // Fetch data from SRAM.
    for (int i = 0; i < 8; i++) {
      read_data[i] = mmio_region_read32(sram_region_main_addr,
                                        i * (ptrdiff_t)sizeof(uint32_t));
    }
    sca_set_trigger_low();
  }
  // Acknowledge test.
  ibex_sca_result_t uj_output;
  uj_output.result = 0;
  RESP_OK(ujson_serialize_ibex_sca_result_t, uj, &uj_output);
  return OK_STATUS();
}

status_t handle_ibex_sca_register_file_write(ujson_t *uj) {
  // Get data to write into RF.
  ibex_sca_test_data_t uj_data;
  TRY(ujson_deserialize_ibex_sca_test_data_t(uj, &uj_data));
  // SCA code target.
  for (int it = 0; it < uj_data.num_iterations; it++) {
    sca_set_trigger_high();
    // Write provided data into register file.
    asm volatile("mv x5, %0" : : "r"(uj_data.data[0]));
    asm volatile("mv x6, %0" : : "r"(uj_data.data[1]));
    asm volatile("mv x7, %0" : : "r"(uj_data.data[2]));
    asm volatile("mv x28, %0" : : "r"(uj_data.data[3]));
    asm volatile("mv x29, %0" : : "r"(uj_data.data[4]));
    asm volatile("mv x30, %0" : : "r"(uj_data.data[5]));
    asm volatile("mv x31, %0" : : "r"(uj_data.data[6]));
    sca_set_trigger_low();
  }
  // Acknowledge test.
  ibex_sca_result_t uj_output;
  uj_output.result = 0;
  RESP_OK(ujson_serialize_ibex_sca_result_t, uj, &uj_output);
  return OK_STATUS();
}

status_t handle_ibex_sca_register_file_read(ujson_t *uj) {
  // Get data to write into RF.
  ibex_sca_test_data_t uj_data;
  TRY(ujson_deserialize_ibex_sca_test_data_t(uj, &uj_data));
  // Initialize temporary registers with reference values.
  asm volatile("mv x5, %0" : : "r"(uj_data.data[0]));
  asm volatile("mv x6, %0" : : "r"(uj_data.data[1]));
  asm volatile("mv x7, %0" : : "r"(uj_data.data[2]));
  asm volatile("mv x28, %0" : : "r"(uj_data.data[3]));
  asm volatile("mv x29, %0" : : "r"(uj_data.data[4]));
  asm volatile("mv x30, %0" : : "r"(uj_data.data[5]));

  // SCA code target.
  for (int it = 0; it < uj_data.num_iterations; it++) {
    sca_set_trigger_high();
    // Copy registers.
    asm volatile("mv x28, x5");
    asm volatile("mv x29, x6");
    asm volatile("mv x30, x7");
    sca_set_trigger_low();
  }
  // Acknowledge test.
  ibex_sca_result_t uj_output;
  uj_output.result = 0;
  RESP_OK(ujson_serialize_ibex_sca_result_t, uj, &uj_output);
  return OK_STATUS();
}

status_t handle_ibex_sca_init(ujson_t *uj) {
  // Setup trigger and enable peripherals needed for the test.
  sca_select_trigger_type(kScaTriggerTypeSw);
  // As we are using the software defined trigger, the first argument of
  // sca_init is not needed. kScaTriggerSourceAes is selected as a placeholder.
  sca_init(kScaTriggerSourceAes, kScaPeripheralIoDiv4 | kScaPeripheralKmac);

  // Disable the instruction cache and dummy instructions for SCA.
  sca_configure_cpu();

  // Read device ID and return to host.
  penetrationtest_device_id_t uj_output;
  TRY(sca_read_device_id(uj_output.device_id));
  RESP_OK(ujson_serialize_penetrationtest_device_id_t, uj, &uj_output);

  return OK_STATUS();
}

status_t handle_ibex_sca(ujson_t *uj) {
  ibex_sca_subcommand_t cmd;
  TRY(ujson_deserialize_ibex_sca_subcommand_t(uj, &cmd));
  switch (cmd) {
    case kIbexScaSubcommandInit:
      return handle_ibex_sca_init(uj);
    case kIbexScaSubcommandRFRead:
      return handle_ibex_sca_register_file_read(uj);
    case kIbexScaSubcommandRFWrite:
      return handle_ibex_sca_register_file_write(uj);
    case kIbexScaSubcommandTLRead:
      return handle_ibex_sca_tl_read(uj);
    case kIbexScaSubcommandTLWrite:
      return handle_ibex_sca_tl_write(uj);
    case kIbexScaSubcommandKeySideloading:
      return handle_ibex_sca_key_sideloading(uj);
    default:
      LOG_ERROR("Unrecognized IBEX SCA subcommand: %d", cmd);
      return INVALID_ARGUMENT();
  }
  return OK_STATUS();
}
