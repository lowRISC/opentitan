// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/silicon_creator/lib/ownership/ownership_unlock.h"

#include "sw/device/lib/base/macros.h"
#include "sw/device/lib/base/memory.h"
#include "sw/device/silicon_creator/lib/boot_data.h"
#include "sw/device/silicon_creator/lib/boot_svc/boot_svc_msg.h"
#include "sw/device/silicon_creator/lib/drivers/hmac.h"
#include "sw/device/silicon_creator/lib/drivers/lifecycle.h"
#include "sw/device/silicon_creator/lib/error.h"
#include "sw/device/silicon_creator/lib/ownership/owner_block.h"
#include "sw/device/silicon_creator/lib/ownership/ownership_key.h"

static hardened_bool_t is_locked_none(uint32_t ownership_state) {
  if (ownership_state == kOwnershipStateLockedOwner ||
      ownership_state == kOwnershipStateUnlockedSelf ||
      ownership_state == kOwnershipStateUnlockedAny ||
      ownership_state == kOwnershipStateUnlockedEndorsed) {
    return kHardenedBoolFalse;
  }
  return kHardenedBoolTrue;
}

static rom_error_t do_unlock(boot_svc_msg_t *msg, boot_data_t *bootdata) {
  // Verify that the nonce is correct.
  if (!nonce_equal(&msg->ownership_unlock_req.nonce, &bootdata->nonce)) {
    return kErrorOwnershipInvalidNonce;
  }

  // Verify the device identification number is correct.
  lifecycle_device_id_t device_id;
  lifecycle_device_id_get(&device_id);
  if (lifecycle_din_eq(&device_id, msg->ownership_unlock_req.din) !=
      kHardenedBoolTrue) {
    return kErrorOwnershipInvalidDin;
  }

  if (msg->ownership_unlock_req.unlock_mode == kBootSvcUnlockEndorsed) {
    hmac_digest_t digest;
    hmac_sha256(&msg->ownership_unlock_req.next_owner_key,
                sizeof(msg->ownership_unlock_req.next_owner_key), &digest);
    memcpy(&bootdata->next_owner, &digest, sizeof(digest));
    bootdata->ownership_state = kOwnershipStateUnlockedEndorsed;
  } else if (msg->ownership_unlock_req.unlock_mode == kBootSvcUnlockAny) {
    bootdata->ownership_state = kOwnershipStateUnlockedAny;
  } else if (msg->ownership_unlock_req.unlock_mode == kBootSvcUnlockUpdate) {
    bootdata->ownership_state = kOwnershipStateUnlockedSelf;
  } else {
    return kErrorOwnershipInvalidMode;
  }
  nonce_new(&bootdata->nonce);
  return kErrorWriteBootdataThenReboot;
}

static rom_error_t unlock(boot_svc_msg_t *msg, boot_data_t *bootdata) {
  size_t len = (uintptr_t)&msg->ownership_unlock_req.signature -
               (uintptr_t)&msg->ownership_unlock_req.unlock_mode;
  if (bootdata->ownership_state == kOwnershipStateLockedOwner) {
    switch (owner_page[0].update_mode) {
      case kOwnershipUpdateModeOpen:
        // The Open mode allows unlock to any unlock state.
        break;
      case kOwnershipUpdateModeNewVersion:
        // The NewVersion mode forbids all unlocks.
        return kErrorOwnershipUnlockDenied;
      case kOwnershipUpdateModeSelf:
      case kOwnershipUpdateModeSelfVersion:
      default:
        // The `unlock` funciton services UnlockAny and UnlockEndorsed requests,
        // neither of which are valid for the `Self` mode.
        return kErrorOwnershipInvalidMode;
    }
    // Check the signature against the unlock key.
    // TODO(cfrantz): Add a mechanism to control whether or not the
    // recovery key is allowed here.
    if (ownership_key_validate(
            /*page=*/0, kOwnershipKeyUnlock | kOwnershipKeyRecovery,
            &msg->ownership_unlock_req.signature,
            &msg->ownership_unlock_req.unlock_mode,
            len) == kHardenedBoolFalse) {
      return kErrorOwnershipInvalidSignature;
    }
    return do_unlock(msg, bootdata);
  } else if (is_locked_none(bootdata->ownership_state) == kHardenedBoolTrue) {
    // In the No-Owner state, we check against the silicon_creator's
    // no_owner_recovery_key.
    if (ownership_key_validate(/*page=*/0, kOwnershipKeyRecovery,
                               &msg->ownership_unlock_req.signature,
                               &msg->ownership_unlock_req.unlock_mode,
                               len) == kHardenedBoolFalse) {
      return kErrorOwnershipInvalidSignature;
    }
    return do_unlock(msg, bootdata);
  } else {
    return kErrorOwnershipInvalidState;
  }
}

static rom_error_t unlock_update(boot_svc_msg_t *msg, boot_data_t *bootdata) {
  size_t len = (uintptr_t)&msg->ownership_unlock_req.signature -
               (uintptr_t)&msg->ownership_unlock_req.unlock_mode;
  if (bootdata->ownership_state == kOwnershipStateLockedOwner) {
    switch (owner_page[0].update_mode) {
      case kOwnershipUpdateModeNewVersion:
        // The NewVersion mode forbids all unlocks.
        return kErrorOwnershipUnlockDenied;
      case kOwnershipUpdateModeSelf:
      case kOwnershipUpdateModeSelfVersion:
      case kOwnershipUpdateModeOpen:
      default:
          // The `unlock_update` funciton services UnlockUpdate update requests,
          // which are valid for the `Open` and `Self` modes.
          ;
    }
    // Check the signature against the unlock key.
    if (ownership_key_validate(/*page=*/0, kOwnershipKeyUnlock,
                               &msg->ownership_unlock_req.signature,
                               &msg->ownership_unlock_req.unlock_mode,
                               len) == kHardenedBoolFalse) {
      return kErrorOwnershipInvalidSignature;
    }
    return do_unlock(msg, bootdata);
  }
  return kErrorOwnershipInvalidState;
}

static rom_error_t unlock_abort(boot_svc_msg_t *msg, boot_data_t *bootdata) {
  size_t len = (uintptr_t)&msg->ownership_unlock_req.signature -
               (uintptr_t)&msg->ownership_unlock_req.unlock_mode;
  if (bootdata->ownership_state == kOwnershipStateUnlockedEndorsed ||
      bootdata->ownership_state == kOwnershipStateUnlockedAny ||
      bootdata->ownership_state == kOwnershipStateUnlockedSelf) {
    // Check the signature against the unlock key.
    if (ownership_key_validate(/*page=*/0, kOwnershipKeyUnlock,
                               &msg->ownership_unlock_req.signature,
                               &msg->ownership_unlock_req.unlock_mode,
                               len) == kHardenedBoolFalse) {
      return kErrorOwnershipInvalidSignature;
    }
    if (!nonce_equal(&msg->ownership_unlock_req.nonce, &bootdata->nonce)) {
      return kErrorOwnershipInvalidNonce;
    }

    // Verify the device identification number is correct.
    lifecycle_device_id_t device_id;
    lifecycle_device_id_get(&device_id);
    if (lifecycle_din_eq(&device_id, msg->ownership_unlock_req.din) !=
        kHardenedBoolTrue) {
      return kErrorOwnershipInvalidDin;
    }
    // Go back to locked owner.
    bootdata->ownership_state = kOwnershipStateLockedOwner;
    nonce_new(&bootdata->nonce);
    return kErrorWriteBootdataThenReboot;
  }
  return kErrorOwnershipInvalidState;
}

rom_error_t ownership_unlock_handler(boot_svc_msg_t *msg,
                                     boot_data_t *bootdata) {
  rom_error_t error = kErrorOwnershipInvalidRequest;
  switch (msg->ownership_unlock_req.unlock_mode) {
    case kBootSvcUnlockAny:
      error = unlock(msg, bootdata);
      break;
    case kBootSvcUnlockEndorsed:
      error = unlock(msg, bootdata);
      break;
    case kBootSvcUnlockUpdate:
      error = unlock_update(msg, bootdata);
      break;
    case kBootSvcUnlockAbort:
      error = unlock_abort(msg, bootdata);
      break;
    default:
        /* nothing */;
  }
  boot_svc_ownership_unlock_res_init(
      error == kErrorWriteBootdataThenReboot ? kErrorOk : error,
      &msg->ownership_unlock_res);
  return error;
}
