// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// This #if define ... ensures backwards compatibility with darjeeling. Either
// both tops will get their own testutils or this define guard can be
// implemented at a more granular level (i.e. at function level).
#if defined(OPENTITAN_IS_DARJEELING)

#include "sw/device/lib/testing/keymgr_dpe_testutils.h"

#include "hw/top/dt/keymgr_dpe.h"
#include "hw/top/dt/otp_ctrl.h"
#include "hw/top/dt/rstmgr.h"
#include "sw/device/lib/dif/dif_keymgr_dpe.h"
#include "sw/device/lib/dif/dif_otp_ctrl.h"
#include "sw/device/lib/dif/dif_rstmgr.h"
#include "sw/device/lib/runtime/ibex.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/otp_ctrl_testutils.h"
#include "sw/device/lib/testing/rstmgr_testutils.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/silicon_creator/lib/base/chip.h"

status_t keymgr_dpe_testutils_startup(dif_keymgr_dpe_t *keymgr_dpe,
                                      uint32_t slot_dst_sel) {
  dif_rstmgr_t rstmgr;
  dif_rstmgr_reset_info_bitfield_t info;

  TRY(dif_rstmgr_init_from_dt(kDtRstmgrAon, &rstmgr));
  info = rstmgr_testutils_reason_get();

  // POR reset.
  if (info == kDifRstmgrResetInfoPor) {
    LOG_INFO(
        "Powered up for the first time, lock SECRET2 and SECRET3 partitions");
    dif_otp_ctrl_t otp;
    TRY(dif_otp_ctrl_init_from_dt(kDtOtpCtrl, &otp));
    TRY(otp_ctrl_testutils_lock_partition(&otp, kDifOtpCtrlPartitionSecret2,
                                          0));
    TRY(otp_ctrl_testutils_lock_partition(&otp, kDifOtpCtrlPartitionSecret3,
                                          0));

    // Reboot device.
    rstmgr_testutils_reason_clear();
    LOG_INFO("Triggering software reset");
    TRY(dif_rstmgr_software_device_reset(&rstmgr));

    // Wait here until device reset.
    wait_for_interrupt();

  } else {
    TRY_CHECK(info == kDifRstmgrResetInfoSw, "Unexpected reset reason: %08x",
              info);
    LOG_INFO(
        "Powered up for the second time, actuate keymgr_dpe and perform test.");

    // Initialize keymgr_dpe context.
    TRY(dif_keymgr_dpe_init_from_dt(kDtKeymgrDpe, keymgr_dpe));

    // Advance to Initialized state.
    TRY(keymgr_dpe_testutils_check_state(keymgr_dpe, kDifKeymgrDpeStateReset));
    TRY(dif_keymgr_dpe_initialize(keymgr_dpe, slot_dst_sel));
    TRY(keymgr_dpe_testutils_wait_for_operation_done(keymgr_dpe));
    TRY(keymgr_dpe_testutils_check_state(keymgr_dpe,
                                         kDifKeymgrDpeStateAvailable));
    LOG_INFO("UDS is latched.");
  }
  return OK_STATUS();
}

status_t keymgr_dpe_testutils_advance_state(
    const dif_keymgr_dpe_t *keymgr_dpe,
    const dif_keymgr_dpe_advance_params_t *params) {
  TRY(dif_keymgr_dpe_advance_state(keymgr_dpe, params));
  return keymgr_dpe_testutils_wait_for_operation_done(keymgr_dpe);
}

status_t keymgr_dpe_testutils_erase_slot(
    const dif_keymgr_dpe_t *keymgr_dpe,
    const dif_keymgr_dpe_erase_params_t *params) {
  TRY(dif_keymgr_dpe_erase_slot(keymgr_dpe, params));
  return keymgr_dpe_testutils_wait_for_operation_done(keymgr_dpe);
}

status_t keymgr_dpe_testutils_generate(
    const dif_keymgr_dpe_t *keymgr_dpe,
    const dif_keymgr_dpe_generate_params_t *params,
    dif_keymgr_dpe_output_t *key) {
  TRY(dif_keymgr_dpe_generate(keymgr_dpe, params));
  TRY(keymgr_dpe_testutils_wait_for_operation_done(keymgr_dpe));
  TRY(dif_keymgr_dpe_read_output(keymgr_dpe, key));
  return OK_STATUS();
}

status_t keymgr_dpe_testutils_check_state(
    const dif_keymgr_dpe_t *keymgr_dpe,
    const dif_keymgr_dpe_state_t exp_state) {
  dif_keymgr_dpe_state_t act_state;
  TRY(dif_keymgr_dpe_get_state(keymgr_dpe, &act_state));
  TRY_CHECK(act_state == exp_state,
            "KeymgrDPE in unexpected state: %x, expected to be %x", act_state,
            exp_state);
  return OK_STATUS();
}

status_t keymgr_dpe_testutils_wait_for_operation_done(
    const dif_keymgr_dpe_t *keymgr_dpe) {
  dif_keymgr_dpe_status_codes_t status;
  do {
    TRY(dif_keymgr_dpe_get_status_codes(keymgr_dpe, &status));
  } while (status == 0);
  TRY_CHECK(status == kDifKeymgrDpeStatusCodeIdle, "Unexpected status: %x",
            status);
  return OK_STATUS();
}

#elif defined(OPENTITAN_IS_EARLGREY) || defined(OPENTITAN_IS_ENGLISHBREAKFAST)
#include "hw/top/dt/otp_ctrl.h"
#include "sw/device/lib/arch/boot_stage.h"
#include "sw/device/lib/dif/dif_flash_ctrl.h"
#include "sw/device/lib/dif/dif_keymgr_dpe.h"
#include "sw/device/lib/dif/dif_otp_ctrl.h"
#include "sw/device/lib/dif/dif_rstmgr.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/entropy_testutils.h"
#include "sw/device/lib/testing/flash_ctrl_testutils.h"
#include "sw/device/lib/testing/keymgr_dpe_testutils.h"
#include "sw/device/lib/testing/kmac_testutils.h"
#include "sw/device/lib/testing/otp_ctrl_testutils.h"
#include "sw/device/lib/testing/rstmgr_testutils.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/silicon_creator/lib/base/chip.h"
#include "sw/device/silicon_creator/lib/drivers/retention_sram.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

#define MODULE_ID MAKE_MODULE_ID('k', 'm', 'd')

enum {
  /** Flash Secret partition ID. */
  kFlashInfoPartitionId = 0,

  /** Secret partition flash bank ID. */
  kFlashInfoBankId = 0,

  /** Creator Secret flash info page ID. */
  kFlashInfoPageIdCreatorSecret = 1,

  /** Owner Secret flash info page ID. */
  kFlashInfoPageIdOwnerSecret = 2,
};

const static char *kKeymgrStageNames[] = {
    [kDifKeymgrDpeStateReset] = "Reset",
    [kDifKeymgrDpeStateAvailable] = "Available",
    [kDifKeymgrDpeStateDisabled] = "Disabled",
    [kDifKeymgrDpeStateInvalid] = "Invalid"};

static status_t write_info_page(dif_flash_ctrl_state_t *flash, uint32_t page_id,
                                const keymgr_dpe_testutils_secret_t *data,
                                bool scramble) {
  uint32_t address = 0;
  if (scramble) {
    TRY(flash_ctrl_testutils_info_region_scrambled_setup(
        flash, page_id, kFlashInfoBankId, kFlashInfoPartitionId, &address));
  } else {
    TRY(flash_ctrl_testutils_info_region_setup(
        flash, page_id, kFlashInfoBankId, kFlashInfoPartitionId, &address));
  }

  TRY(flash_ctrl_testutils_erase_and_write_page(
      flash, address, kFlashInfoPartitionId, data->value,
      kDifFlashCtrlPartitionTypeInfo, ARRAYSIZE(data->value)));

  keymgr_dpe_testutils_secret_t readback_data;
  TRY(flash_ctrl_testutils_read(
      flash, address, kFlashInfoPartitionId, readback_data.value,
      kDifFlashCtrlPartitionTypeInfo, ARRAYSIZE(readback_data.value), 0));
  TRY_CHECK(memcmp(data->value, readback_data.value, sizeof(data->value)) == 0);
  return OK_STATUS();
}

status_t keymgr_dpe_testutils_flash_init(
    dif_flash_ctrl_state_t *flash,
    const keymgr_dpe_testutils_secret_t *creator_secret,
    const keymgr_dpe_testutils_secret_t *owner_secret) {
  // Initialize flash secrets.
  if (creator_secret) {
    TRY(write_info_page(flash, kFlashInfoPageIdCreatorSecret, creator_secret,
                        /*scramble=*/true));
  }
  TRY(write_info_page(flash, kFlashInfoPageIdOwnerSecret, owner_secret,
                      /*scramble=*/true));
  return OK_STATUS();
}

static status_t check_lock_otp_partition(void) {
  dif_otp_ctrl_t otp;
  TRY(dif_otp_ctrl_init_from_dt(kDtOtpCtrl, &otp));

  bool is_computed;
  TRY(dif_otp_ctrl_is_digest_computed(&otp, kDifOtpCtrlPartitionSecret2,
                                      &is_computed));
  if (is_computed) {
    uint64_t digest;
    TRY(dif_otp_ctrl_get_digest(&otp, kDifOtpCtrlPartitionSecret2, &digest));
    LOG_INFO("OTP partition locked. Digest: %x-%x", ((uint32_t *)&digest)[0],
             ((uint32_t *)&digest)[1]);
    return OK_STATUS();
  }

  TRY(otp_ctrl_testutils_lock_partition(&otp, kDifOtpCtrlPartitionSecret2, 0));
  return OK_STATUS();
}

static status_t dif_init(dif_keymgr_dpe_t *keymgr_dpe, dif_kmac_t *kmac) {
  // Initialize KMAC in preparation for keymgr use.
  TRY(dif_kmac_init(mmio_region_from_addr(TOP_EARLGREY_KMAC_BASE_ADDR), kmac));

  // We shouldn't use the KMAC block's default entropy setting for keymgr, so
  // configure it to use software entropy (and a sideloaded key, although it
  // shouldn't matter here and tests should reconfigure if needed).
  TRY(kmac_testutils_config(kmac, /*sideload=*/true));

  // Initialize keymgr context.
  TRY(dif_keymgr_dpe_init(
      mmio_region_from_addr(TOP_EARLGREY_KEYMGR_DPE_BASE_ADDR), keymgr_dpe));
  return OK_STATUS();
}

/**
 * Wrapper around the erase slot call.
 */
status_t keymgr_dpe_testutils_erase_slot(
    const dif_keymgr_dpe_t *keymgr_dpe,
    const dif_keymgr_dpe_erase_params_t *params) {
  TRY(dif_keymgr_dpe_erase_slot(keymgr_dpe, params));
  return keymgr_dpe_testutils_wait_for_operation_done(keymgr_dpe);
}

status_t keymgr_dpe_initialize_sim_dv(dif_keymgr_dpe_t *keymgr_dpe,
                                      dif_kmac_t *kmac) {
  // Initialize keymgr and advance to CreatorRootKey state.
  TRY(keymgr_dpe_testutils_startup(keymgr_dpe, kmac));
  LOG_INFO("Keymgr DPE generated the CreatorRootKey in slot %d",
           kCreatorRootKeyParams.slot_dst_sel);
  // Generate key at CreatorRootKey (to follow same sequence and reuse
  // chip_sw_keymgr_key_derivation_vseq.sv).
  TRY(keymgr_dpe_testutils_generate_key(keymgr_dpe, &kKeyVersionedParams));
  LOG_INFO("Keymgr DPE generated key at CreatorRootKey State");

  // Advance to OwnerIntermediateKey state and check that the state is correct.
  // The sim_dv testbench expects this state.
  TRY(keymgr_dpe_testutils_advance_state(keymgr_dpe, &kOwnerIntKeyParams));
  LOG_INFO("Keymgr DPE generated the OwnerIntKey in slot %d",
           kOwnerIntKeyParams.slot_dst_sel);
  return OK_STATUS();
}

status_t keymgr_dpe_initialize_sival(dif_keymgr_dpe_t *keymgr_dpe,
                                     dif_kmac_t *kmac) {
  dif_keymgr_dpe_state_t keymgr_dpe_state;

  // keymgr_dpe should have loaded the Creator Key after this function
  TRY(keymgr_dpe_testutils_try_startup(keymgr_dpe, kmac, &keymgr_dpe_state));

  // Advance the Creator Key to the Owner Int Key
  TRY(keymgr_dpe_testutils_advance_state(keymgr_dpe, &kOwnerIntKeyParams));

  // Advance the Owner Int Key to the Owner Key
  TRY(keymgr_dpe_testutils_advance_state(keymgr_dpe, &kOwnerKeyParams));

  return keymgr_dpe_testutils_check_state(keymgr_dpe,
                                          kDifKeymgrDpeStateAvailable);
}

status_t keymgr_dpe_testutils_initialize(dif_keymgr_dpe_t *keymgr_dpe,
                                         dif_kmac_t *kmac) {
  if (kBootStage == kBootStageOwner) {
    return keymgr_dpe_initialize_sival(keymgr_dpe, kmac);
  }
  // All other configurations use the sim_dv initialization.
  return keymgr_dpe_initialize_sim_dv(keymgr_dpe, kmac);
}

status_t keymgr_dpe_testutils_try_startup(
    dif_keymgr_dpe_t *keymgr_dpe, dif_kmac_t *kmac,
    dif_keymgr_dpe_state_t *keymgr_dpe_state) {
  TRY(dif_init(keymgr_dpe, kmac));

  // Check keymgr dpe state. If initialized, there is no need to proceed with
  // the initialization process.
  TRY(dif_keymgr_dpe_get_state(keymgr_dpe, keymgr_dpe_state));

  if (*keymgr_dpe_state == kDifKeymgrDpeStateInvalid ||
      *keymgr_dpe_state == kDifKeymgrDpeStateDisabled) {
    LOG_INFO("Unexpected keymgr dpe state: 0x%x", *keymgr_dpe_state);
    return INTERNAL();
  }

  if (*keymgr_dpe_state == kDifKeymgrDpeStateReset) {
    TRY(keymgr_dpe_testutils_startup(keymgr_dpe, kmac));
    TRY(dif_keymgr_dpe_get_state(keymgr_dpe, keymgr_dpe_state));
  }

  return OK_STATUS();
}

status_t keymgr_dpe_testutils_init_nvm_then_reset(void) {
  dif_flash_ctrl_state_t flash;
  dif_rstmgr_t rstmgr;
  dif_otp_ctrl_t otp_ctrl;

  TRY(dif_rstmgr_init(mmio_region_from_addr(TOP_EARLGREY_RSTMGR_AON_BASE_ADDR),
                      &rstmgr));
  const dif_rstmgr_reset_info_bitfield_t reset_info =
      rstmgr_testutils_reason_get();

  // POR reset.
  if (reset_info == kDifRstmgrResetInfoPor) {
    LOG_INFO("Powered up for the first time, program flash");

    TRY(dif_flash_ctrl_init_state(
        &flash, mmio_region_from_addr(TOP_EARLGREY_FLASH_CTRL_CORE_BASE_ADDR)));
    TRY(dif_otp_ctrl_init(
        mmio_region_from_addr(TOP_EARLGREY_OTP_CTRL_CORE_BASE_ADDR),
        &otp_ctrl));

    bool secret2_computed = false;
    TRY(dif_otp_ctrl_is_digest_computed(&otp_ctrl, kDifOtpCtrlPartitionSecret2,
                                        &secret2_computed));

    // Only initialise the creator secret if `SECRET2` digest has not been
    // computed. `flash_ctrl` will throw a recoverable error if we try to write
    // this afterwards.
    const keymgr_dpe_testutils_secret_t *creator_secret = NULL;
    if (!secret2_computed) {
      creator_secret = &kCreatorSecret;
    }
    TRY(keymgr_dpe_testutils_flash_init(&flash, creator_secret, &kOwnerSecret));

    TRY(check_lock_otp_partition());

    // Reboot device.
    LOG_INFO(
        "Requesting a reset to make OTP partitions accessible to keymgr DPE");
    rstmgr_testutils_reason_clear();
    TRY(dif_rstmgr_software_device_reset(&rstmgr));

    // Wait here until device reset.
    wait_for_interrupt();

    // Should never reach this.
    return INTERNAL();

  } else {
    // Not POR reset: this function has done its job (or can't run because it's
    // supposed to run after POR).
    return OK_STATUS();
  }
}

status_t keymgr_dpe_testutils_startup(dif_keymgr_dpe_t *keymgr_dpe,
                                      dif_kmac_t *kmac) {
  dif_rstmgr_t rstmgr;

  // Check the last word of the retention SRAM creator area to determine the
  // type of the ROM.
  bool is_using_test_rom =
      retention_sram_get()
          ->creator
          .reserved[ARRAYSIZE((retention_sram_t){0}.creator.reserved) - 1] ==
      TEST_ROM_IDENTIFIER;

  TRY(keymgr_dpe_testutils_init_nvm_then_reset());

  TRY(dif_rstmgr_init(mmio_region_from_addr(TOP_EARLGREY_RSTMGR_AON_BASE_ADDR),
                      &rstmgr));
  const dif_rstmgr_reset_info_bitfield_t info = rstmgr_testutils_reason_get();

  TRY_CHECK(info == kDifRstmgrResetInfoSw, "Unexpected reset reason: %08x",
            info);

  LOG_INFO("Initializing entropy complex in Auto mode");

  TRY(entropy_testutils_auto_mode_init());

  LOG_INFO(
      "Powered up for the second time, actuate keymgr dpe and perform test.");

  TRY(dif_init(keymgr_dpe, kmac));

  // Advance to CreatorRootKey state.
  if (is_using_test_rom) {
    // Verify keymgr_dpe state and load UDS into predefined hw slot
    LOG_INFO("Using test_rom, setting inputs and advancing state...");
    TRY(keymgr_dpe_testutils_check_state(keymgr_dpe, kDifKeymgrDpeStateReset));
    TRY(keymgr_dpe_testutils_initial_load_uds(keymgr_dpe, &kInitialParams));
    TRY(keymgr_dpe_testutils_check_state(keymgr_dpe,
                                         kDifKeymgrDpeStateAvailable));
    LOG_INFO("Keymgr DPE loaded the UDS and entered Available state.");

    // Generate the creator root key
    TRY(keymgr_dpe_testutils_advance_state(keymgr_dpe, &kCreatorRootKeyParams));
    LOG_INFO("Keymgr DPE testutils derived the CreatorRootKey");
  } else {
    LOG_INFO("Using ROM");
    LOG_INFO(
        "The keymgr DPE should already contain the derived CreatorRootKey");
  }

  // Key generation is not really necessary for all tests, but it is
  // added to make sure each test using this function is also compatible with
  // the DV_WAIT sequences from keymgr_key_derivation vseq
  TRY(keymgr_dpe_testutils_generate_key(keymgr_dpe, &kKeyVersionedParams));
  LOG_INFO("Keymgr DPE generated sw key from the CreatorRootKey");

  return OK_STATUS();
}

/**
 * Wrapper around the initial advance call. It is not possible to subsidize
 * this call with a normal advance call as the rtl does not handle them
 * equally. If writing to any lockable register (sw-binding, max key version,
 * policy register) then these locks are not removed after the initial advance
 * call completes.
 */
// TODO(#30665): Verify if the max key version needs to be written here too!
// When loading the UDS the RTL fetches the max key version from the SW
// register. Verify that the lock is released when the version register is
// locked.
status_t keymgr_dpe_testutils_initial_load_uds(
    const dif_keymgr_dpe_t *keymgr_dpe,
    const dif_keymgr_dpe_advance_params_t *params) {
  TRY(dif_keymgr_dpe_initialize(keymgr_dpe, params->slot_dst_sel));
  return keymgr_dpe_testutils_wait_for_operation_done(keymgr_dpe);
}

status_t keymgr_dpe_testutils_advance_state(
    const dif_keymgr_dpe_t *keymgr_dpe,
    const dif_keymgr_dpe_advance_params_t *params) {
  TRY(dif_keymgr_dpe_advance_state(keymgr_dpe, params));
  return keymgr_dpe_testutils_wait_for_operation_done(keymgr_dpe);
}

status_t keymgr_dpe_testutils_check_state(
    const dif_keymgr_dpe_t *keymgr_dpe,
    const dif_keymgr_dpe_state_t exp_state) {
  dif_keymgr_dpe_state_t act_state;
  TRY(dif_keymgr_dpe_get_state(keymgr_dpe, &act_state));
  TRY_CHECK(act_state == exp_state,
            "Keymgr DPE in unexpected state: %x, expected to be %x", act_state,
            exp_state);
  return OK_STATUS();
}

status_t keymgr_dpe_testutils_generate_key(
    const dif_keymgr_dpe_t *keymgr_dpe,
    const dif_keymgr_dpe_generate_params_t *params) {
  TRY(dif_keymgr_dpe_generate(keymgr_dpe, params));
  return keymgr_dpe_testutils_wait_for_operation_done(keymgr_dpe);
}

status_t keymgr_dpe_testutils_disable(const dif_keymgr_dpe_t *keymgr_dpe) {
  TRY(dif_keymgr_dpe_disable(keymgr_dpe));
  TRY(keymgr_dpe_testutils_wait_for_operation_done(keymgr_dpe));
  TRY(keymgr_dpe_testutils_check_state(keymgr_dpe, kDifKeymgrDpeStateDisabled));
  return OK_STATUS();
}

status_t keymgr_dpe_testutils_wait_for_operation_done(
    const dif_keymgr_dpe_t *keymgr_dpe) {
  dif_keymgr_dpe_status_codes_t status;
  do {
    TRY(dif_keymgr_dpe_get_status_codes(keymgr_dpe, &status));
  } while (status == 0);
  // If status code indicate any error (not only idle flag is set) then this
  // try_check will fail!
  TRY_CHECK(status == kDifKeymgrDpeStatusCodeIdle, "Unexpected status: %x",
            status);
  return OK_STATUS();
}

status_t keymgr_dpe_testutils_state_string_get(
    const dif_keymgr_dpe_t *keymgr_dpe, const char **stage_name) {
  dif_keymgr_dpe_state_t state;
  CHECK_DIF_OK(dif_keymgr_dpe_get_state(keymgr_dpe, &state));

  if (state >= ARRAYSIZE(kKeymgrStageNames)) {
    *stage_name = NULL;
    return INTERNAL();
  }

  *stage_name = kKeymgrStageNames[state];
  return OK_STATUS();
}

status_t keymgr_dpe_testutils_clear_sideload_key(
    const dif_keymgr_dpe_t *keymgr_dpe,
    dif_keymgr_dpe_sideload_clr_t clear_dest) {
  TRY(dif_keymgr_dpe_clear_sideload_key(keymgr_dpe, clear_dest));
  return OK_STATUS();
}
#else
#error "[Keymgr_dpe, testutils] None of the supported tops defined!"
#endif
