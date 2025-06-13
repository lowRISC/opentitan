// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/silicon_creator/rom_ext/rom_ext_boot_services.h"

#include "sw/device/silicon_creator/lib/boot_data.h"
#include "sw/device/silicon_creator/lib/boot_log.h"
#include "sw/device/silicon_creator/lib/boot_svc/boot_svc_msg.h"
#include "sw/device/silicon_creator/lib/drivers/lifecycle.h"
#include "sw/device/silicon_creator/lib/error.h"
#include "sw/device/silicon_creator/lib/manifest.h"
#include "sw/device/silicon_creator/lib/ownership/ownership_activate.h"
#include "sw/device/silicon_creator/lib/ownership/ownership_unlock.h"
#include "sw/device/silicon_creator/lib/rescue/rescue.h"
#include "sw/device/silicon_creator/rom_ext/rom_ext_boot_policy.h"
#include "sw/device/silicon_creator/rom_ext/rom_ext_boot_policy_ptrs.h"

OT_WARN_UNUSED_RESULT
static rom_error_t boot_svc_next_boot_bl0_slot_handler(
    boot_svc_msg_t *boot_svc_msg, boot_data_t *boot_data, boot_log_t *boot_log,
    lifecycle_state_t lc_state) {
  uint32_t active_slot = boot_data->primary_bl0_slot;
  uint32_t primary_slot = boot_svc_msg->next_boot_bl0_slot_req.primary_bl0_slot;
  rom_error_t error = kErrorOk;

  // If the requested primary slot is the same as the active slot, this request
  // is a no-op.
  if (active_slot != primary_slot) {
    switch (primary_slot) {
      case kBootSlotA:
      case kBootSlotB:
        boot_data->primary_bl0_slot = primary_slot;
        // Write boot data, updating relevant fields and recomputing the digest.
        HARDENED_RETURN_IF_ERROR(boot_data_write(boot_data));
        // Read the boot data back to ensure the correct slot is booted this
        // time.
        HARDENED_RETURN_IF_ERROR(boot_data_read(lc_state, boot_data));
        // Update the boot log.
        boot_log->primary_bl0_slot = boot_data->primary_bl0_slot;
        break;
      case kBootSlotUnspecified:
        // Do nothing.
        break;
      default:
        error = kErrorBootSvcBadSlot;
    }
  }

  // Record the new primary slot for use in the response message.
  active_slot = boot_data->primary_bl0_slot;

  uint32_t next_slot = boot_svc_msg->next_boot_bl0_slot_req.next_bl0_slot;
  switch (launder32(next_slot)) {
    case kBootSlotA:
    case kBootSlotB:
      // We overwrite the RAM copy of the primary slot to the requested next
      // slot. This will cause a one-time boot of the requested side.
      boot_data->primary_bl0_slot = next_slot;
      break;
    case kBootSlotUnspecified:
      // Do nothing.
      break;
    default:
      error = kErrorBootSvcBadSlot;
  }

  boot_svc_next_boot_bl0_slot_res_init(error, active_slot,
                                       &boot_svc_msg->next_boot_bl0_slot_res);
  // We always return OK here because we've logged any error status in the boot
  // services response message and we want the boot flow to continue.
  return kErrorOk;
}

OT_WARN_UNUSED_RESULT
static rom_error_t boot_svc_min_sec_ver_handler(
    boot_svc_msg_t *boot_svc_msg, boot_data_t *boot_data,
    lifecycle_state_t lc_state, owner_application_keyring_t *keyring,
    size_t *verify_key, owner_config_t *owner_config,
    uint32_t *isfb_check_count) {
  const uint32_t current_min_sec_ver = boot_data->min_security_version_bl0;
  const uint32_t requested_min_sec_ver =
      boot_svc_msg->next_boot_bl0_slot_req.next_bl0_slot;

  // Ensure the requested minimum security version isn't lower than the current
  // minimum security version.
  if (launder32(requested_min_sec_ver) > current_min_sec_ver) {
    HARDENED_CHECK_GT(requested_min_sec_ver, current_min_sec_ver);
    uint32_t max_sec_ver = current_min_sec_ver;

    // Check the two flash slots for valid manifests and determine the maximum
    // value of the new minimum_security_version.  This prevents a malicious
    // MinBl0SecVer request from making the chip un-bootable.
    const manifest_t *manifest = rom_ext_boot_policy_manifest_a_get();
    uint32_t flash_exec = 0;
    rom_error_t error =
        rom_ext_verify(manifest, boot_data, &flash_exec, keyring, verify_key,
                       owner_config, isfb_check_count);
    if (error == kErrorOk && manifest->security_version > max_sec_ver) {
      max_sec_ver = manifest->security_version;
    }
    manifest = rom_ext_boot_policy_manifest_b_get();
    error = rom_ext_verify(manifest, boot_data, &flash_exec, keyring,
                           verify_key, owner_config, isfb_check_count);
    if (error == kErrorOk && manifest->security_version > max_sec_ver) {
      max_sec_ver = manifest->security_version;
    }

    if (requested_min_sec_ver <= max_sec_ver) {
      HARDENED_CHECK_LE(requested_min_sec_ver, max_sec_ver);
      // Update boot data to the requested minimum BL0 security version.
      boot_data->min_security_version_bl0 = requested_min_sec_ver;

      // Write boot data, updating relevant fields and recomputing the digest.
      HARDENED_RETURN_IF_ERROR(boot_data_write(boot_data));
      // Read the boot data back to ensure the correct policy is used this boot.
      HARDENED_RETURN_IF_ERROR(boot_data_read(lc_state, boot_data));

      boot_svc_min_bl0_sec_ver_res_init(boot_data->min_security_version_bl0,
                                        kErrorOk,
                                        &boot_svc_msg->min_bl0_sec_ver_res);

      HARDENED_CHECK_EQ(requested_min_sec_ver,
                        boot_data->min_security_version_bl0);
      return kErrorOk;
    }
  }
  boot_svc_min_bl0_sec_ver_res_init(current_min_sec_ver, kErrorBootSvcBadSecVer,
                                    &boot_svc_msg->min_bl0_sec_ver_res);
  return kErrorOk;
}

OT_WARN_UNUSED_RESULT
rom_error_t boot_svc_handler(boot_svc_msg_t *boot_svc_msg,
                             boot_data_t *boot_data, boot_log_t *boot_log,
                             lifecycle_state_t lc_state,
                             owner_application_keyring_t *keyring,
                             size_t *verify_key, owner_config_t *owner_config,
                             uint32_t *isfb_check_count) {
  // TODO(lowRISC#22387): Examine the boot_svc code paths for boot loops.
  if (boot_svc_msg->header.identifier == kBootSvcIdentifier) {
    HARDENED_RETURN_IF_ERROR(boot_svc_header_check(&boot_svc_msg->header));
    uint32_t msg_type = boot_svc_msg->header.type;
    switch (launder32(msg_type)) {
      case kBootSvcEmptyReqType:
        HARDENED_CHECK_EQ(msg_type, kBootSvcEmptyReqType);
        boot_svc_empty_res_init(&boot_svc_msg->empty);
        break;
      case kBootSvcEnterRescueReqType:
        HARDENED_CHECK_EQ(msg_type, kBootSvcEnterRescueReqType);
        return rescue_enter_handler(boot_svc_msg);
      case kBootSvcNextBl0SlotReqType:
        HARDENED_CHECK_EQ(msg_type, kBootSvcNextBl0SlotReqType);
        return boot_svc_next_boot_bl0_slot_handler(boot_svc_msg, boot_data,
                                                   boot_log, lc_state);
      case kBootSvcMinBl0SecVerReqType:
        HARDENED_CHECK_EQ(msg_type, kBootSvcMinBl0SecVerReqType);
        return boot_svc_min_sec_ver_handler(boot_svc_msg, boot_data, lc_state,
                                            keyring, verify_key, owner_config,
                                            isfb_check_count);
      case kBootSvcOwnershipUnlockReqType:
        HARDENED_CHECK_EQ(msg_type, kBootSvcOwnershipUnlockReqType);
        return ownership_unlock_handler(boot_svc_msg, boot_data);
      case kBootSvcOwnershipActivateReqType:
        HARDENED_CHECK_EQ(msg_type, kBootSvcOwnershipActivateReqType);
        return ownership_activate_handler(boot_svc_msg, boot_data);
      case kBootSvcEmptyResType:
      case kBootSvcEnterRescueResType:
      case kBootSvcNextBl0SlotResType:
      case kBootSvcMinBl0SecVerResType:
      case kBootSvcOwnershipUnlockResType:
      case kBootSvcOwnershipActivateResType:
        // For response messages left in ret-ram we do nothing.
        break;
      default:
          // For messages with an unknown msg_type, we do nothing.
          ;
    }
  }
  return kErrorOk;
}
