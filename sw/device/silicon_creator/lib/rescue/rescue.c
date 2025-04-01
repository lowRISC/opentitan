// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/silicon_creator/lib/rescue/rescue.h"

#include "sw/device/lib/arch/device.h"
#include "sw/device/lib/base/memory.h"
#include "sw/device/silicon_creator/lib/boot_data.h"
#include "sw/device/silicon_creator/lib/boot_log.h"
#include "sw/device/silicon_creator/lib/boot_svc/boot_svc_enter_rescue.h"
#include "sw/device/silicon_creator/lib/boot_svc/boot_svc_msg.h"
#include "sw/device/silicon_creator/lib/dbg_print.h"
#include "sw/device/silicon_creator/lib/drivers/flash_ctrl.h"
#include "sw/device/silicon_creator/lib/drivers/ibex.h"
#include "sw/device/silicon_creator/lib/drivers/lifecycle.h"
#include "sw/device/silicon_creator/lib/drivers/pinmux.h"
#include "sw/device/silicon_creator/lib/drivers/retention_sram.h"
#include "sw/device/silicon_creator/lib/drivers/rstmgr.h"
#include "sw/device/silicon_creator/lib/drivers/uart.h"
#include "sw/device/silicon_creator/lib/manifest.h"
#include "sw/device/silicon_creator/lib/ownership/datatypes.h"
#include "sw/device/silicon_creator/lib/ownership/owner_block.h"

#include "hw/top/flash_ctrl_regs.h"

typedef enum rescue_request {
  kRescueRequestNone = 0,
  kRescueRequestEnter = 0x739,
  kRescueRequestSkip = 0x1d4,
} rescue_request_t;

static rescue_request_t rescue_requested;

const uint32_t kFlashPageSize = FLASH_CTRL_PARAM_BYTES_PER_PAGE;
const uint32_t kFlashBankSize =
    kFlashPageSize * FLASH_CTRL_PARAM_REG_PAGES_PER_BANK;

static inline bool is_rom_ext(const void *data) {
  const manifest_t *manifest = (const manifest_t *)data;
  return manifest->identifier == CHIP_ROM_EXT_IDENTIFIER;
}

static inline bool is_rom_ext_update_allowed(rescue_state_t *state) {
  // A ROM_EXT update is allowed if the partition we're flashing is not the
  // ROM_EXT active partition.
  return (state->mode == kRescueModeFirmware &&
          state->boot_log->rom_ext_slot == kBootSlotB) ||
         (state->mode == kRescueModeFirmwareSlotB &&
          state->boot_log->rom_ext_slot == kBootSlotA);
}

rom_error_t flash_firmware_block(rescue_state_t *state) {
  uint32_t bank_offset =
      state->mode == kRescueModeFirmwareSlotB ? kFlashBankSize : 0;
  if (state->flash_offset == 0) {
    // TODO(#24428): Make sure we interact correctly with owner flash region
    // configuration.
    flash_ctrl_data_default_perms_set((flash_ctrl_perms_t){
        .read = kMultiBitBool4True,
        .write = kMultiBitBool4True,
        .erase = kMultiBitBool4True,
    });
    // Detect if we're allowed to flash the ROM_EXT _and_ if the data stream
    // starts with a ROM_EXT.  If so, we start flashing at offset 0 in this
    // bank.
    state->flash_begin =
        (is_rom_ext_update_allowed(state) && is_rom_ext(state->data))
            ? 0
            : state->flash_start;

    // Erase the allowed range in the requested partition.
    for (uint32_t addr = state->flash_begin; addr < state->flash_limit;
         addr += kFlashPageSize) {
      HARDENED_RETURN_IF_ERROR(
          flash_ctrl_data_erase(bank_offset + addr, kFlashCtrlEraseTypePage));
    }
    // Regardless of whether we're allowed to flash the ROM_EXT, set the flash
    // offset to zero if the data stream contains a ROM_EXT, otherwise, set to
    // flash_start. This will allow rescue to silently consume the ROM_EXT if
    // we're in the ROM_EXT active partition.
    state->flash_offset = is_rom_ext(state->data) ? 0 : state->flash_start;
  }

  if (state->flash_offset < state->flash_begin) {
    // Before allowed beginning; silently consume the data without flashing.
    state->flash_offset += sizeof(state->data);
  } else if (state->flash_offset >= state->flash_limit) {
    // Beyond the allowed limit; return an error.
    return kErrorRescueImageTooBig;
  } else {
    // In the allowed range; flash the data.
    HARDENED_RETURN_IF_ERROR(flash_ctrl_data_write(
        bank_offset + state->flash_offset,
        sizeof(state->data) / sizeof(uint32_t), state->data));
    state->flash_offset += sizeof(state->data);
  }
  return kErrorOk;
}

rom_error_t flash_owner_block(rescue_state_t *state) {
  if (state->bootdata->ownership_state == kOwnershipStateUnlockedAny ||
      state->bootdata->ownership_state == kOwnershipStateUnlockedSelf ||
      state->bootdata->ownership_state == kOwnershipStateUnlockedEndorsed ||
      (state->bootdata->ownership_state == kOwnershipStateLockedOwner &&
       owner_block_newversion_mode() == kHardenedBoolTrue)) {
    HARDENED_RETURN_IF_ERROR(flash_ctrl_info_erase(
        &kFlashCtrlInfoPageOwnerSlot1, kFlashCtrlEraseTypePage));
    HARDENED_RETURN_IF_ERROR(flash_ctrl_info_write(
        &kFlashCtrlInfoPageOwnerSlot1, 0,
        sizeof(state->data) / sizeof(uint32_t), state->data));
  } else {
    dbg_printf("error: cannot accept owner_block in current state\r\n");
  }
  return kErrorOk;
}

#ifdef ROM_EXT_KLOBBER_ALLOWED
// In order to facilitate debuging and manual test flows for ownerhsip transfer,
// we allow the owner pages to be erased if and only if the chip is in the DEV
// lifecycle state AND the ROM_EXT was specifically built to allow owner erase.
//
// In the general case, the `KLBR` command does not exist.  It can only be
// enabled by silicon_creator and only for DEV chips.
static void ownership_erase(void) {
  lifecycle_state_t lc_state = lifecycle_state_get();
  if (lc_state == kLcStateDev) {
    OT_DISCARD(flash_ctrl_info_erase(&kFlashCtrlInfoPageOwnerSlot0,
                                     kFlashCtrlEraseTypePage));
    OT_DISCARD(flash_ctrl_info_erase(&kFlashCtrlInfoPageOwnerSlot1,
                                     kFlashCtrlEraseTypePage));
    dbg_printf("ok: erased owner blocks\r\n");
  } else {
    dbg_printf("error: erase not allowed in state %x\r\n", lc_state);
  }
}
#endif

rom_error_t rescue_validate_mode(uint32_t mode, rescue_state_t *state) {
  dbg_printf("\r\nmode: %C\r\n", bitfield_byteswap32(mode));
  rom_error_t result = kErrorOk;

  // The following commands are always allowed and are not subject to
  // the "command allowed" check.
  switch (mode) {
    case kRescueModeReboot:
      dbg_printf("ok: reboot\r\n");
      state->mode = (rescue_mode_t)mode;
      goto exitproc;
#ifdef ROM_EXT_KLOBBER_ALLOWED
    case kRescueModeKlobber:
      ownership_erase();
      goto exitproc;
#endif
    default:
        /* do nothing */;
  }

  hardened_bool_t allow = owner_rescue_command_allowed(state->config, mode);
  if (allow == kHardenedBoolTrue) {
    switch (mode) {
      case kRescueModeBootLog:
        dbg_printf("ok: receive boot_log\r\n");
        break;
      case kRescueModeBootSvcRsp:
        dbg_printf("ok: receive boot_svc response\r\n");
        break;
      case kRescueModeBootSvcReq:
        dbg_printf("ok: send boot_svc request\r\n");
        break;
      case kRescueModeOwnerBlock:
        if (state->bootdata->ownership_state == kOwnershipStateUnlockedAny ||
            state->bootdata->ownership_state == kOwnershipStateUnlockedSelf ||
            state->bootdata->ownership_state ==
                kOwnershipStateUnlockedEndorsed ||
            (state->bootdata->ownership_state == kOwnershipStateLockedOwner &&
             owner_block_newversion_mode() == kHardenedBoolTrue)) {
          dbg_printf("ok: send owner_block\r\n");
        } else {
          dbg_printf("error: cannot accept owner_block in current state\r\n");
          return kErrorRescueBadMode;
        }
        break;
      case kRescueModeFirmware:
      case kRescueModeFirmwareSlotB:
        dbg_printf("ok: send firmware\r\n");
        break;
      case kRescueModeOwnerPage0:
      case kRescueModeOwnerPage1:
        dbg_printf("ok: receive owner page\r\n");
        break;
      case kRescueModeOpenTitanID:
        dbg_printf("ok: receive device ID\r\n");
        break;
      default:
        // User input error.  Do not change modes.
        dbg_printf("error: unrecognized mode\r\n");
        return kErrorRescueBadMode;
    }
    state->mode = (rescue_mode_t)mode;
  } else {
    dbg_printf("error: mode not allowed\r\n");
    result = kErrorRescueBadMode;
  }
exitproc:
  state->frame = 1;
  state->offset = 0;
  state->flash_offset = 0;
  return result;
}

rom_error_t rescue_send_handler(rescue_state_t *state) {
  hardened_bool_t allow =
      owner_rescue_command_allowed(state->config, state->mode);
  if (allow != kHardenedBoolTrue) {
    return kErrorRescueBadMode;
  }

  const retention_sram_t *rr = retention_sram_get();
  switch (state->mode) {
    case kRescueModeBootLog:
      memcpy(state->data, &rr->creator.boot_log, sizeof(rr->creator.boot_log));
      state->staged_len = sizeof(rr->creator.boot_log);
      break;
    case kRescueModeBootSvcRsp:
      memcpy(state->data, &rr->creator.boot_svc_msg,
             sizeof(rr->creator.boot_svc_msg));
      state->staged_len = sizeof(rr->creator.boot_svc_msg);
      break;
    case kRescueModeOpenTitanID: {
      lifecycle_device_id_get((lifecycle_device_id_t *)state->data);
      state->staged_len = sizeof(lifecycle_device_id_t);
      break;
    }
    case kRescueModeOwnerPage0:
    case kRescueModeOwnerPage1:
      HARDENED_RETURN_IF_ERROR(flash_ctrl_info_read(
          state->mode == kRescueModeOwnerPage0 ? &kFlashCtrlInfoPageOwnerSlot0
                                               : &kFlashCtrlInfoPageOwnerSlot1,
          0, sizeof(state->data) / sizeof(uint32_t), state->data));
      state->staged_len = sizeof(state->data);
      break;

    case kRescueModeBootSvcReq:
    case kRescueModeOwnerBlock:
    case kRescueModeFirmware:
    case kRescueModeFirmwareSlotB:
      // Nothing to do for receive modes.
      return kErrorOk;
    case kRescueModeReboot:
      // If a reboot was requested, return an error and go through the normal
      // shutdown process.
      return kErrorRescueReboot;
    default:
      // This state should be impossible.
      return kErrorRescueBadMode;
  }
  return kErrorRescueSendStart;
}

rom_error_t rescue_recv_handler(rescue_state_t *state) {
  hardened_bool_t allow =
      owner_rescue_command_allowed(state->config, state->mode);
  if (allow != kHardenedBoolTrue) {
    return kErrorRescueBadMode;
  }

  retention_sram_t *rr = retention_sram_get();
  switch (state->mode) {
    case kRescueModeBootLog:
    case kRescueModeBootSvcRsp:
    case kRescueModeOpenTitanID:
    case kRescueModeOwnerPage0:
    case kRescueModeOwnerPage1:
      // Nothing to do for send modes.
      break;
    case kRescueModeBootSvcReq:
      if (state->offset >= sizeof(rr->creator.boot_svc_msg)) {
        const boot_svc_msg_t *msg = (const boot_svc_msg_t *)state->data;
        allow = owner_rescue_command_allowed(state->config, msg->header.type);
        if (allow != kHardenedBoolTrue) {
          return kErrorRescueBadMode;
        }
        memcpy(&rr->creator.boot_svc_msg, state->data,
               sizeof(rr->creator.boot_svc_msg));
        state->offset = 0;
      }
      break;
    case kRescueModeOwnerBlock:
      if (state->offset == sizeof(state->data)) {
        HARDENED_RETURN_IF_ERROR(flash_owner_block(state));
        state->offset = 0;
      }
      break;
    case kRescueModeFirmware:
    case kRescueModeFirmwareSlotB:
      if (state->offset == sizeof(state->data)) {
        HARDENED_RETURN_IF_ERROR(flash_firmware_block(state));
        state->offset = 0;
      }
      break;
    case kRescueModeReboot:
    default:
      // This state should be impossible.
      return kErrorRescueBadMode;
  }
  return kErrorOk;
}

void rescue_state_init(rescue_state_t *state, boot_data_t *bootdata,
                       boot_log_t *boot_log,
                       const owner_rescue_config_t *config) {
  state->boot_log = boot_log;
  state->bootdata = bootdata;
  state->config = config;
  if ((hardened_bool_t)config == kHardenedBoolFalse) {
    HARDENED_CHECK_EQ((hardened_bool_t)config, kHardenedBoolFalse);
    // If there is no rescue config, then the rescue region starts immediately
    // after the ROM_EXT and ends at the end of the flash bank.
    state->flash_start = CHIP_ROM_EXT_SIZE_MAX;
    state->flash_limit = kFlashBankSize;
    state->inactivity_deadline = 0;
  } else {
    state->flash_start = (uint32_t)config->start * kFlashPageSize;
    state->flash_limit =
        (uint32_t)(config->start + config->size) * kFlashPageSize;
    uint32_t timeout =
        bitfield_field32_read(config->timeout, RESCUE_TIMEOUT_SECONDS);
    state->inactivity_deadline =
        timeout ? ibex_mcycle() + ibex_time_to_cycles(1000000 * timeout) : 0;
  }
}

rom_error_t rescue_enter_handler(boot_svc_msg_t *msg) {
  rescue_requested = msg->enter_rescue_req.skip_once == kHardenedBoolTrue
                         ? kRescueRequestSkip
                         : kRescueRequestEnter;
  boot_svc_enter_rescue_res_init(kErrorOk, &msg->enter_rescue_res);
  return kErrorOk;
}

rom_error_t rescue_inactivity(rescue_state_t *state) {
  if (state->inactivity_deadline &&
      ibex_mcycle() > state->inactivity_deadline) {
    return kErrorRescueInactivity;
  }
  return kErrorOk;
}

hardened_bool_t rescue_enter_on_fail(const owner_rescue_config_t *config) {
  if ((hardened_bool_t)config != kHardenedBoolFalse) {
    if (bitfield_bit32_read(config->timeout, RESCUE_ENTER_ON_FAIL_BIT)) {
      return kHardenedBoolTrue;
    }
  }
  return kHardenedBoolFalse;
}

void rescue_skip_next_boot(void) {
  boot_svc_msg_t *msg = &retention_sram_get()->creator.boot_svc_msg;
  boot_svc_enter_rescue_req_init(kHardenedBoolTrue, &msg->enter_rescue_req);
}

hardened_bool_t rescue_detect_entry(const owner_rescue_config_t *config) {
  switch (rescue_requested) {
    case kRescueRequestEnter:
      return kHardenedBoolTrue;
    case kRescueRequestSkip:
      return kHardenedBoolFalse;
    default:
        /* do nothing and continue with trigger detection */;
  }
  rescue_protocol_t protocol = kRescueProtocolXmodem;
  rescue_detect_t detect = kRescueDetectBreak;
  uint32_t index = 0;
  uint32_t gpio_val = 0;
  if ((hardened_bool_t)config != kHardenedBoolFalse) {
    protocol = config->protocol;
    detect = bitfield_field32_read(config->detect, RESCUE_DETECT);
    index = bitfield_field32_read(config->detect, RESCUE_DETECT_INDEX);
    gpio_val = bitfield_bit32_read(config->gpio, RESCUE_GPIO_VALUE_BIT);
  }
  dbg_printf("info: rescue protocol %c\r\n", rescue_type);
  if (protocol != rescue_type) {
    dbg_printf("warning: rescue configured for protocol %c\r\n", protocol);
  }
  switch (detect) {
    case kRescueDetectNone:
      break;
    case kRescueDetectBreak:
      if (uart_break_detect(kRescueDetectTime) == kHardenedBoolTrue) {
        dbg_printf("rescue:1.0 remember to clear break\r\n");
        uart_enable_receiver();
        return kHardenedBoolTrue;
      }
      break;
    case kRescueDetectGpio:
      if (pinmux_read_gpio(0) == gpio_val) {
        return kHardenedBoolTrue;
      }
      break;
    case kRescueDetectStrap:
      if (pinmux_read_straps() == index) {
        return kHardenedBoolTrue;
      }
      break;
  }
  return kHardenedBoolFalse;
}
