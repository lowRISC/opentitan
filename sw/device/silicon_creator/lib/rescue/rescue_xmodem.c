// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/arch/device.h"
#include "sw/device/lib/base/memory.h"
#include "sw/device/silicon_creator/lib/boot_data.h"
#include "sw/device/silicon_creator/lib/drivers/rstmgr.h"
#include "sw/device/silicon_creator/lib/drivers/uart.h"
#include "sw/device/silicon_creator/lib/ownership/datatypes.h"
#include "sw/device/silicon_creator/lib/rescue/rescue.h"
#include "sw/device/silicon_creator/lib/rescue/xmodem.h"

// All of the xmodem functions accept an opaque iohandle pointer.
// The iohandle is used to facilitate unit tests and doesn't have
// any function in real firmware.
#define iohandle NULL

static void change_speed(void) {
  dbg_printf("ok: waiting for baudrate\r\n");
  uint32_t speed = 0;
  OT_DISCARD(uart_read((uint8_t *)&speed, sizeof(speed), 10000));
  uint32_t nco;
  switch (speed) {
    case kRescueBaud115K:
      nco = kUartBaud115K;
      break;
    case kRescueBaud230K:
      nco = kUartBaud230K;
      break;
    case kRescueBaud460K:
      nco = kUartBaud460K;
      break;
    case kRescueBaud921K:
      nco = kUartBaud921K;
      break;
    case kRescueBaud1M33:
      nco = kUartBaud1M33;
      break;
    case kRescueBaud1M50:
      nco = kUartBaud1M50;
      break;
    default:
      nco = 0;
  }
  if (nco) {
    dbg_printf("ok: new baudrate %C\r\n", speed);
    uart_init(nco);
    uart_enable_receiver();
  } else {
    dbg_printf("error: unsupported baudrate %C\r\n", speed);
  }
}

static rom_error_t validate_mode(uint32_t mode, rescue_state_t *state,
                                 boot_data_t *bootdata) {
  if (mode == kRescueModeBaud) {
    change_speed();
    return kErrorOk;
  }
  return rescue_validate_mode(mode, state, bootdata);
}

static rom_error_t handle_send_modes(rescue_state_t *state,
                                     boot_data_t *bootdata) {
  rom_error_t error = rescue_send_handler(state, bootdata);
  if (error == kErrorRescueSendStart && state->staged_len > 0) {
    error = xmodem_send(iohandle, state->data, state->staged_len);
    state->staged_len = 0;
    validate_mode(kRescueModeFirmware, state, bootdata);
  }
  return error;
}

static rom_error_t handle_recv_modes(rescue_state_t *state,
                                     boot_data_t *bootdata) {
  rom_error_t error = rescue_recv_handler(state, bootdata);
  if (error == kErrorRescueImageTooBig || error == kErrorRescueBadMode) {
    xmodem_cancel(iohandle);
  }
  return error;
}

static rom_error_t protocol(rescue_state_t *state, boot_data_t *bootdata) {
  rom_error_t result;
  size_t rxlen;
  uint8_t command;
  uint32_t next_mode = 0;

  state->reboot = true;
  validate_mode(kRescueModeFirmware, state, bootdata);

  xmodem_recv_start(iohandle);
  while (true) {
    HARDENED_RETURN_IF_ERROR(handle_send_modes(state, bootdata));
    result = xmodem_recv_frame(
        iohandle, state->frame, state->data + state->offset,
        sizeof(state->data) - state->offset, &rxlen, &command);
    if (state->frame == 1 && result == kErrorXModemTimeoutStart) {
      xmodem_recv_start(iohandle);
      continue;
    }
    switch (result) {
      case kErrorOk:
        // Packet ok.
        state->offset += rxlen;
        HARDENED_RETURN_IF_ERROR(handle_recv_modes(state, bootdata));
        xmodem_ack(iohandle, true);
        break;
      case kErrorXModemEndOfFile:
        if (state->offset % 2048 != 0) {
          // If there is unhandled residue, extend out to a full block and
          // then handle it.
          while (state->offset % 2048 != 0) {
            state->data[state->offset++] = 0xFF;
          }
          HARDENED_RETURN_IF_ERROR(handle_recv_modes(state, bootdata));
        }
        xmodem_ack(iohandle, true);
        if (!state->reboot) {
          state->frame = 1;
          state->offset = 0;
          state->flash_offset = 0;
          continue;
        }
        return kErrorRescueReboot;
      case kErrorXModemCrc:
        xmodem_ack(iohandle, false);
        continue;
      case kErrorXModemCancel:
        return result;
      case kErrorXModemUnknown:
        if (state->frame == 1) {
          if (command == '\r') {
            validate_mode(next_mode, state, bootdata);
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

rom_error_t rescue_protocol(boot_data_t *bootdata,
                            const owner_rescue_config_t *config) {
  rescue_state_t rescue_state;
  rescue_state_init(&rescue_state, config);
  rom_error_t result = protocol(&rescue_state, bootdata);
  if (result == kErrorRescueReboot) {
    rstmgr_reset();
  }
  return result;
}
