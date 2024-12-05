// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include <stdbool.h>
#include <stdint.h>
#include <string.h>

#include "sw/device/lib/testing/keymgr_testutils.h"
#include "sw/device/lib/testing/otbn_testutils.h"
#include "sw/device/lib/testing/ret_sram_testutils.h"
#include "sw/device/lib/testing/rstmgr_testutils.h"
#include "sw/device/lib/testing/sram_ctrl_testutils.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"
#include "sw/device/silicon_creator/lib/drivers/retention_sram.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

static dif_keymgr_t keymgr;
static dif_kmac_t kmac;
static dif_otbn_t otbn;
static dif_rstmgr_t rstmgr;
static dif_sram_ctrl_t sram_ctrl;

enum {
  kKeymgrOutputSizeWords = 8,
  kKeymgrOutputSizeBytes = 32,

  kX2551PublicKeySizeBytes = 32,

  // The retention SRAM testutils allocate some internal data as well as a
  // number of counters; both of which should not be overwritten by this
  // test. Hence, the actual base address is offset to account for this.
  kRetSramBaseAddr = TOP_EARLGREY_RAM_RET_AON_BASE_ADDR +
                     offsetof(retention_sram_t, owner) +
                     4 * kRetSramTestutilsNumberOfCounters,

// Compile-time directive to choose between CDI flow types. The default
// derivation type is sealing.
#ifndef DERIVE_ATTESTATION
  kCdiType = kDifKeymgrSealingCdi
#else
  kCdiType = kDifKeymgrAttestationCdi
#endif
};

/**
 * Grouping of the three CDI output variants that can be generated in
 * each key manager state (identity, versioned software key, sideload OTBN key).
 *
 * Note that the sideload OTBN key is not visible to software. In order to
 * run the same verification steps as for the identity and software keys, a
 * X25519 public key is generated in the OTBN and retrieved. For the sake of
 * simplicity, and only in the confines of this test, we can assume that the
 * X25519 public key and the sideload OTBN key refer to the same thing.
 */
typedef struct cdi_outputs {
  dif_keymgr_output_t identity;
  dif_keymgr_output_t sw_key;
  uint32_t sideload_key[kX2551PublicKeySizeBytes];
} cdi_outputs_t;

// Symbols of the OTBN X22519 public key generation program.
// See sw/otbn/crypto/x25519_sideload.s for the source code.
OTBN_DECLARE_APP_SYMBOLS(x25519_sideload);
OTBN_DECLARE_SYMBOL_ADDR(x25519_sideload, enc_u);
OTBN_DECLARE_SYMBOL_ADDR(x25519_sideload, enc_result);
static const otbn_app_t kOtbnAppX25519 = OTBN_APP_T_INIT(x25519_sideload);
static const otbn_addr_t kOtbnVarEncU =
    OTBN_ADDR_T_INIT(x25519_sideload, enc_u);
static const otbn_addr_t kOtbnVarEncResult =
    OTBN_ADDR_T_INIT(x25519_sideload, enc_result);

OTTF_DEFINE_TEST_CONFIG();

/**
 * Initialize the dif handles required for this test.
 */
static void init_peripheral_handles(void) {
  // The testutils initialize the key manager and KMAC handles.
  CHECK_STATUS_OK(keymgr_testutils_initialize(&keymgr, &kmac));

  // Reconfigure the KMAC to use the EDN entropy source as opposed to a
  // software-provided one as is default in the testutils.
  dif_kmac_config_t config = {
      .entropy_mode = kDifKmacEntropyModeEdn,
      .entropy_fast_process = true,
      .sideload = true,
  };
  CHECK_DIF_OK(dif_kmac_configure(&kmac, config));

  CHECK_DIF_OK(dif_rstmgr_init(
      mmio_region_from_addr(TOP_EARLGREY_RSTMGR_AON_BASE_ADDR), &rstmgr));
  CHECK_DIF_OK(dif_sram_ctrl_init(
      mmio_region_from_addr(TOP_EARLGREY_SRAM_CTRL_RET_AON_REGS_BASE_ADDR),
      &sram_ctrl));
  CHECK_DIF_OK(
      dif_otbn_init(mmio_region_from_addr(TOP_EARLGREY_OTBN_BASE_ADDR), &otbn));
}

/**
 * Equality check of two masked key manager outputs without unmasking.
 *
 * @param output_a First key manager output.
 * @param output_b Second key manager output.
 * @return Result of the equality check.
 */
static bool compare_outputs(const dif_keymgr_output_t *output_a,
                            const dif_keymgr_output_t *output_b) {
  uint32_t scratch[kKeymgrOutputSizeWords];
  for (int i = 0; i < kKeymgrOutputSizeWords; i++) {
    // Check whether two masked keys are equal without unmasking them:
    //
    // output_a0 = k0 + m0, output_a1 = m0
    // output_b0 = k1 + m1, output_b1 = m1
    // t = output_a0 + output_b0 = m0 + m1
    // 0 = t ^ output_a1 ^ output_b1
    //
    // In order to prevent an accidental unmasking through reordering of the
    // operation after compilation, `t` is read into an auxiliary array.
    scratch[i] = output_a->value[0][i] ^ output_b->value[0][i];
    if ((scratch[i] ^ output_a->value[1][i] ^ output_b->value[1][i]) != 0x0) {
      return false;
    }
  }
  return true;
}

/**
 * Write a `cdi_outputs_t` object into the retention SRAM at a specific offset
 * from `kRetSramBaseAddr`. The offset then is incremented by the size of the
 * written data.
 *
 * @param outputs The CDI outputs to be stored.
 * @param offset The offset from `kRetSramBaseAddr`.
 */
static void ret_sram_write_keys(const cdi_outputs_t *outputs, size_t *offset) {
  uint32_t buf[sizeof(cdi_outputs_t)];
  memcpy(buf, outputs, sizeof(cdi_outputs_t));

  sram_ctrl_testutils_write(
      kRetSramBaseAddr + *offset,
      (sram_ctrl_testutils_data_t){.words = buf, .len = sizeof(cdi_outputs_t)});
  *offset += sizeof(cdi_outputs_t);
}

/**
 * Read a `cdi_outputs_t` object from the retention SRAM at a specific offset
 * from `kRetSramBaseAddr`. The offset then is incremented by the size of the
 * read data.
 *
 * @param outputs The destination of the read CDI outputs.
 * @param offset The offset from `kRetSramBaseAddr`.
 */
static void ret_sram_read_keys(cdi_outputs_t *outputs, size_t *offset) {
  memcpy(outputs, (uint8_t *)(kRetSramBaseAddr + *offset),
         sizeof(cdi_outputs_t));
  *offset += sizeof(cdi_outputs_t);
}

/**
 * Invoke the generation of an CDI identity and read it back.
 *
 * @param state_name The current key manager state string.
 * @param identity The destination of the read identity.
 */
static void derive_identity(const char *state_name,
                            dif_keymgr_output_t *identity) {
  CHECK_STATUS_OK(keymgr_testutils_generate_identity(
      &keymgr, (dif_keymgr_identity_seed_params_t){.cdi_type = kCdiType}));
  LOG_INFO("Keymgr generated identity at %s State", state_name);

  CHECK_DIF_OK(dif_keymgr_read_output(&keymgr, identity));
}

/**
 * Invoke the generation of a CDI versioned software key and read it back.
 * A second generation with an invalid key version should fail.
 *
 * @param state_name The current key manager state string.
 * @param key The destination of the read software key.
 */
static void derive_sw_key(const char *state_name, dif_keymgr_output_t *key) {
  uint32_t max_version;
  CHECK_STATUS_OK(keymgr_testutils_max_key_version_get(&keymgr, &max_version));

  dif_keymgr_versioned_key_params_t params = kKeyVersionedParams;
  params.dest = kDifKeymgrVersionedKeyDestSw;
  params.version = max_version;
  params.cdi_type = kCdiType;

  CHECK_STATUS_OK(keymgr_testutils_generate_versioned_key(&keymgr, params));
  LOG_INFO("Keymgr generated SW output at %s State", state_name);

  CHECK_DIF_OK(dif_keymgr_read_output(&keymgr, key));

#ifndef DERIVE_ATTESTATION
  // If the key version is larger than the permitted maximum version, then
  // the key generation must fail.
  params.version += 1;
  CHECK_STATUS_NOT_OK(keymgr_testutils_generate_versioned_key(&keymgr, params));
#endif
}

/**
 * Invoke the generation of sideload OTBN key, run the X25519 OTBN program and
 * read back the resulting public key. A second generation with an invalid key
 * version should fail.
 *
 * @param state_name The current key manager state string.
 * @param The destination of the read X25519 public key.
 */
static void derive_sideload_otbn_key(const char *state_name,
                                     uint32_t key[kKeymgrOutputSizeWords]) {
  uint32_t max_version;
  CHECK_STATUS_OK(keymgr_testutils_max_key_version_get(&keymgr, &max_version));

  dif_keymgr_versioned_key_params_t params = kKeyVersionedParams;
  params.dest = kDifKeymgrVersionedKeyDestOtbn;
  params.version = max_version;

  CHECK_STATUS_OK(keymgr_testutils_generate_versioned_key(&keymgr, params));
  LOG_INFO("Keymgr generated HW output for Otbn at %s State", state_name);

  // Run the X25519 public key generation. For more details, see the OTBN
  // sideload test sw/device/tests/keymgr_sideload_otbn_test.c.
  CHECK_STATUS_OK(otbn_testutils_load_app(&otbn, kOtbnAppX25519));
  CHECK_DIF_OK(dif_otbn_set_ctrl_software_errs_fatal(&otbn, false));

  const uint32_t kEncodedU[8] = {
      // Montgomery u-Coordinate.
      0x9, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0,
  };
  CHECK_STATUS_OK(otbn_testutils_write_data(&otbn, sizeof(kEncodedU),
                                            &kEncodedU, kOtbnVarEncU));
  LOG_INFO("Starting OTBN program...");
  CHECK_DIF_OK(dif_otbn_set_ctrl_software_errs_fatal(&otbn, false));
  CHECK_STATUS_OK(otbn_testutils_execute(&otbn));
  CHECK_STATUS_OK(otbn_testutils_wait_for_done(&otbn, 0));
  CHECK_STATUS_OK(otbn_testutils_read_data(&otbn, kX2551PublicKeySizeBytes,
                                           kOtbnVarEncResult, key));

#ifndef DERIVE_ATTESTATION
  // If the key version is larger than the permitted maximum version, then
  // the key generation must fail.
  params.version += 1;
  CHECK_STATUS_NOT_OK(keymgr_testutils_generate_versioned_key(&keymgr, params));
#endif
}

/**
 * Derive a CDI identity, software key and sideload OTBN key. If the `write`
 * flag is set, then the keys are written at specific offset in the retention
 * SRAM. In the other case, the generated outputs are compared against outputs
 * from the retention SRAM (corresponding to a run before the reset). Pre- and
 * post- prefix outputs should match. If some previous outputs are provided from
 * an earlier key manager state, compare that the newly generated ones differ.
 *
 * @param state_name The current key manager state string.
 * @param prev_outputs Generated outptus from a previous key manager state.
 * @param offset The offset at which to read or write in the retention SRAM.
 * @param write Indicating whether to write the new keys to the retention SRAM.
 * @param next_outputs The destination of the newly generated CDI outputs.
 */
static void derive_keys(const char *state_name,
                        const cdi_outputs_t *prev_outputs, size_t *offset,
                        bool write, cdi_outputs_t *next_outputs) {
  derive_identity(state_name, &next_outputs->identity);
  derive_sw_key(state_name, &next_outputs->sw_key);
  derive_sideload_otbn_key(state_name, next_outputs->sideload_key);

  if (prev_outputs) {
    CHECK(!compare_outputs(&prev_outputs->identity, &next_outputs->identity));
    CHECK(!compare_outputs(&prev_outputs->sw_key, &next_outputs->sw_key));
    CHECK_ARRAYS_NE(prev_outputs->sideload_key, next_outputs->sideload_key,
                    kKeymgrOutputSizeWords);
  }

  if (write) {
    ret_sram_write_keys(next_outputs, offset);
  } else {
    cdi_outputs_t scratch;
    ret_sram_read_keys(&scratch, offset);

    CHECK(compare_outputs(&scratch.identity, &next_outputs->identity));
    CHECK(compare_outputs(&scratch.sw_key, &next_outputs->sw_key));
    CHECK_ARRAYS_EQ(scratch.sideload_key, next_outputs->sideload_key,
                    kKeymgrOutputSizeWords);
  }
}

/**
 * This test implements both the `chip_sw_keymgr_derive_sealing` and
 * `chip_sw_keymgr_derive_attestation` testplan items, i.e.,
 * verifies the validity of the sealing and attestation CDI flows. The
 * individual testpoint requirements are as follows:
 *
 * - For each keymgr operational state: `CreatorRootKey`, `OwnerIntKey` and
 *   `OwnerKey`:
 *   - Generate identity SW output for the Attestation CDI.
 *   - Generate SW output for the Attestation CDI.
 *   - Generate OTBN sideload output for the Attestation CDI.
 *
 * The creation of the three outputs is handled by the `derive_identity`,
 * `derive_sw_key` and `derive_sideload_otbn_key` functions, which are invoked
 * by `derive_keys` through `test_derive_cdi` that traverses the three
 * operational states.
 *
 * - Ensure that the key output changes after calculating the previous steps
 *   after a keymgr advance operation.
 *
 * The generated CDI outputs in state `i` are passed to state `i+1` and checked
 * in `derive_keys` that they differ.
 *
 * - The keymgr shall be able to reproduce the same keys for a give device
 *   configuration and known set of inputs.
 *
 * The CDI outputs in each state are written into the retention SRAM. After
 * having cycled through all the states, a software reset is performed and
 * CDI output generation is repeated making sure that the same keys are being
 * created (same as the keys in the retention SRAM from the first run) as the
 * device configuration and inputs are unchanged. Reading/writing and key
 * comparison all happen in `derive_keys`.
 *
 * - The software binding registers must be locked after configuration until a
 *   keymgr advance operation.
 *
 * This check is implemented in the keymgr DIF (see `dif_keymgr_advance_state`).
 *
 * - OTP SECRET2 partition (which contains the CREATOR_ROOT_KEY) and flash info
 *   pages 1 and 2 in partition 0 must be configured, otherwise the keymgr will
 * fail to advance into operational states.
 *
 * The provisioning of the device secrets in the OTP SECRET2 partition is
 * handled by the Bazel execution environment, and the flash info secrets are
 * handled by the keymgr testutils (see `keymgr_testutils_init_nvm_then_reset`).
 *
 * - Ensure the entropy complex is running in continuous mode, and that KMAC is
 *   configured to extract entropy from EDN.
 *
 * This is configured in the keymgr testutils (see `keymgr_testutils_startup`)
 * and in `init_peripheral_handles`.
 *
 * - The test should check for any error or fault code status, to ensure all
 *   operations executed successfully.
 *
 * Every API call to either the keymgr testutils or the DIF is checked for its
 * correctness.
 *
 * @param reset_counter Indicator of the test phase.
 */
static void test_derive_cdi(size_t reset_counter) {
  const char *state_name;

  dif_keymgr_state_t keymgr_state;
  CHECK_DIF_OK(dif_keymgr_get_state(&keymgr, &keymgr_state));

  cdi_outputs_t curr_outputs;
  cdi_outputs_t next_outputs;

  size_t offset = 0;
  const bool write = reset_counter == 0;

  switch (keymgr_state) {
    case kDifKeymgrStateCreatorRootKey:

      CHECK_STATUS_OK(keymgr_testutils_state_string_get(&keymgr, &state_name));
      LOG_INFO("Keymgr entered %s State", state_name);

      derive_keys(state_name, NULL, &offset, write, &curr_outputs);

      CHECK_STATUS_OK(
          keymgr_testutils_advance_state(&keymgr, &kOwnerIntParams));

      OT_FALLTHROUGH_INTENDED;
    case kDifKeymgrStateOwnerIntermediateKey:

      CHECK_STATUS_OK(keymgr_testutils_state_string_get(&keymgr, &state_name));
      LOG_INFO("Keymgr entered %s State", state_name);

      derive_keys(state_name,
                  // If the initial key manager state is smaller than
                  // the current one, verify that the new keys differ
                  // from the previous ones.
                  keymgr_state < kDifKeymgrStateOwnerIntermediateKey
                      ? &curr_outputs
                      : NULL,
                  &offset, write, &next_outputs);
      memcpy(&curr_outputs, &next_outputs, sizeof(cdi_outputs_t));

      CHECK_STATUS_OK(
          keymgr_testutils_advance_state(&keymgr, &kOwnerRootKeyParams));

      OT_FALLTHROUGH_INTENDED;
    case kDifKeymgrStateOwnerRootKey:

      CHECK_STATUS_OK(keymgr_testutils_state_string_get(&keymgr, &state_name));
      LOG_INFO("Keymgr entered %s State", state_name);

      derive_keys(
          state_name,
          keymgr_state < kDifKeymgrStateOwnerRootKey ? &curr_outputs : NULL,
          &offset, write, &next_outputs);

      break;
    default:
      // Theoretically, the key manager can boot into an earlier state
      // (`kDifKeymgrStateReset` or `kDifKeymgrStateInitialized`). This is not
      // supported by the testutils and thus must not occur here.
      CHECK(0, "unexpected key manager state %u", keymgr_state);
  }
}

bool test_main(void) {
  const dif_rstmgr_reset_info_bitfield_t reset_info =
      rstmgr_testutils_reason_get();
  size_t reset_counter;

  // Reset the reset counter after the first power up.
  if (reset_info == kDifRstmgrResetInfoPor) {
    CHECK_STATUS_OK(ret_sram_testutils_counter_clear(0));
  }
  CHECK_STATUS_OK(ret_sram_testutils_counter_get(0, &reset_counter));

  init_peripheral_handles();

  test_derive_cdi(reset_counter);

  // Increment the reset counter then reset the device.
  if (reset_counter == 0) {
    CHECK_STATUS_OK(ret_sram_testutils_counter_increment(0));
    CHECK_DIF_OK(dif_rstmgr_software_device_reset(&rstmgr));
    wait_for_interrupt();
  }

  return true;
}
