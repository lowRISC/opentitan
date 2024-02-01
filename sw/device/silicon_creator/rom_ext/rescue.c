// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/silicon_creator/rom_ext/rescue.h"

#include "sw/device/lib/base/memory.h"
#include "sw/device/silicon_creator/lib/dbg_print.h"
#include "sw/device/silicon_creator/lib/drivers/flash_ctrl.h"
#include "sw/device/silicon_creator/lib/drivers/retention_sram.h"
#include "sw/device/silicon_creator/lib/drivers/rstmgr.h"
#include "sw/device/silicon_creator/lib/xmodem.h"

#include "flash_ctrl_regs.h"

// All of the xmodem functions accept an opaque iohandle pointer.
// The iohandle is used to facilitate unit tests and doesn't have
// any function in real firmware.
#define iohandle NULL

static rescue_state_t rescue_state;

rom_error_t flash_firmware_block(rescue_state_t *state) {
  if (state->flash_offset == 0) {
    flash_ctrl_data_default_perms_set((flash_ctrl_perms_t){
        .read = kMultiBitBool4True,
        .write = kMultiBitBool4True,
        .erase = kMultiBitBool4True,
    });
    for (uint32_t addr = state->flash_start; addr < state->flash_limit;
         addr += FLASH_CTRL_PARAM_BYTES_PER_PAGE) {
      HARDENED_RETURN_IF_ERROR(
          flash_ctrl_data_erase(addr, kFlashCtrlEraseTypePage));
    }
    state->flash_offset = state->flash_start;
  }
  if (state->flash_offset < state->flash_limit) {
    HARDENED_RETURN_IF_ERROR(flash_ctrl_data_write(
        state->flash_offset, sizeof(state->data) / sizeof(uint32_t),
        state->data));
    state->flash_offset += sizeof(state->data);
  } else {
    return kErrorRescueImageTooBig;
  }
  return kErrorOk;
}

rom_error_t flash_owner_block(rescue_state_t *state) {
  // FIXME: validate that we're in a state capable of accepting an owner
  // block and validate the block before flashing it.
  HARDENED_RETURN_IF_ERROR(flash_ctrl_info_erase(&kFlashCtrlInfoPageOwnerSlot1,
                                                 kFlashCtrlEraseTypePage));
  HARDENED_RETURN_IF_ERROR(flash_ctrl_info_write(
      &kFlashCtrlInfoPageOwnerSlot1, 0, sizeof(state->data) / sizeof(uint32_t),
      state->data));
  return kErrorOk;
}

static void validate_mode(uint32_t mode, rescue_state_t *state) {
  char *m = (char *)&mode;
  dbg_printf("\r\nmode: %C%C%C%C\r\n", m[3], m[2], m[1], m[0]);
  switch (mode) {
    case kRescueModeBootLog:
      dbg_printf("ok: receive boot_log via xmodem-crc\r\n");
      break;
    case kRescueModeBootSvcRsp:
      dbg_printf("ok: receive boot_svc response via xmodem-crc\r\n");
      break;
    case kRescueModeBootSvcReq:
      dbg_printf("ok: send boot_svc request via xmodem-crc\r\n");
      break;
    case kRescueModeOwnerBlock:
      dbg_printf("ok: send owner_block via xmodem-crc\r\n");
      break;
    case kRescueModeFirmware:
      dbg_printf("ok: send firmware via xmodem-crc\r\n");
      break;
    case kRescueModeReboot:
      dbg_printf("ok: reboot\r\n");
      break;
    case kRescueModeDWIM:
      // Easter egg :)
      dbg_printf("error: i don't know what you mean\r\n");
      return;
    default:
      // User input error.  Do not change modes.
      dbg_printf("error: unrecognized mode\r\n");
      return;
  }
  state->mode = (rescue_mode_t)mode;
  state->frame = 1;
  state->offset = 0;
  state->flash_offset = 0;
}

static rom_error_t handle_send_modes(rescue_state_t *state) {
  const retention_sram_t *rr = retention_sram_get();
  switch (state->mode) {
    case kRescueModeBootLog:
      HARDENED_RETURN_IF_ERROR(xmodem_send(iohandle, &rr->creator.boot_log,
                                           sizeof(rr->creator.boot_log)));
      break;
    case kRescueModeBootSvcRsp:
      HARDENED_RETURN_IF_ERROR(xmodem_send(iohandle, &rr->creator.boot_svc_msg,
                                           sizeof(rr->creator.boot_svc_msg)));
      break;
    case kRescueModeBootSvcReq:
    case kRescueModeOwnerBlock:
    case kRescueModeFirmware:
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
  validate_mode(kRescueModeFirmware, state);
  return kErrorOk;
}

static rom_error_t handle_recv_modes(rescue_state_t *state) {
  retention_sram_t *rr = retention_sram_get();
  switch (state->mode) {
    case kRescueModeBootLog:
    case kRescueModeBootSvcRsp:
      // Nothing to do for send modes.
      break;
    case kRescueModeBootSvcReq:
      if (state->offset >= sizeof(rr->creator.boot_svc_msg)) {
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

static rom_error_t protocol(rescue_state_t *state) {
  rom_error_t result;
  size_t rxlen;
  uint8_t command;
  uint32_t next_mode = 0;

  validate_mode(kRescueModeFirmware, &rescue_state);

  // The rescue region starts immediately after the ROM_EXT and ends
  // at the end of the flash bank.
  // TODO(cfrantz): This needs to be owner-configurable.
  state->flash_start = 0x10000;
  state->flash_limit = 0x80000;

  xmodem_recv_start(iohandle);
  while (true) {
    HARDENED_RETURN_IF_ERROR(handle_send_modes(&rescue_state));
    result = xmodem_recv_frame(iohandle, state->frame,
                               state->data + state->offset, &rxlen, &command);
    if (state->frame == 1 && result == kErrorXModemTimeoutStart) {
      xmodem_recv_start(iohandle);
      continue;
    }
    switch (result) {
      case kErrorOk:
        // Packet ok.
        state->offset += rxlen;
        HARDENED_RETURN_IF_ERROR(handle_recv_modes(&rescue_state));
        xmodem_ack(iohandle, true);
        break;
      case kErrorXModemEndOfFile:
        if (state->offset % 2048 != 0) {
          // If there is unhandled residue, extend out to a full block and
          // then handle it.
          while (state->offset % 2048 != 0) {
            state->data[state->offset++] = 0xFF;
          }
          HARDENED_RETURN_IF_ERROR(handle_recv_modes(&rescue_state));
        }
        xmodem_ack(iohandle, true);
        return kErrorRescueReboot;
      case kErrorXModemCrc:
        xmodem_ack(iohandle, false);
        continue;
      case kErrorXModemCancel:
        return result;
      case kErrorXModemUnknown:
        if (state->frame == 1) {
          if (command == '\r') {
            validate_mode(next_mode, &rescue_state);
            next_mode = 0;
          } else {
            next_mode = (next_mode << 8) | command;
          }
          continue;
        }
        OT_FALLTHROUGH_INTENDED;
      default:
        return result;
    }
    state->frame += 1;
  }
}

rom_error_t rescue_protocol(void) {
  rom_error_t result = protocol(&rescue_state);
  if (result == kErrorRescueReboot) {
    rstmgr_reset();
  }
  return result;
}
