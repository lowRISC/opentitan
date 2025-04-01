// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include <stdbool.h>
#include <stdint.h>
#include <string.h>

#include "sw/device/lib/arch/device.h"
#include "sw/device/lib/base/macros.h"
#include "sw/device/silicon_creator/lib/boot_data.h"
#include "sw/device/silicon_creator/lib/dbg_print.h"
#include "sw/device/silicon_creator/lib/drivers/lifecycle.h"
#include "sw/device/silicon_creator/lib/drivers/rstmgr.h"
#include "sw/device/silicon_creator/lib/drivers/spi_device.h"
#include "sw/device/silicon_creator/lib/drivers/usb.h"
#include "sw/device/silicon_creator/lib/error.h"
#include "sw/device/silicon_creator/lib/rescue/dfu.h"
#include "sw/device/silicon_creator/lib/rescue/rescue.h"
#include "sw/device/silicon_creator/lib/rescue/sfdp.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

const uint32_t rescue_type = kRescueProtocolSpiDfu;

enum {
  /**
   * Base address of the spi_device registers.
   */
  kBase = TOP_EARLGREY_SPI_DEVICE_BASE_ADDR,
  /**
   * The flash buffer is a 2K region within the egress buffer, starting at the
   * beginning of the egress buffer.
   */
  kFlashBuffer = 0,
  /**
   * The mailbox buffer is a 1K region within the egress buffer starting at 2K
   */
  kMailboxBuffer = 2048,
  /**
   * The mailbox address is located at SPI address 0x800.
   */
  kMailboxAddress = 0x800,
};

extern uint32_t spi_device_control(void);

void dfu_transport_data(dfu_ctx_t *ctx, usb_dir_t dir, void *data, size_t len,
                        usb_transfer_flags_t flags) {
  if (dir & kUsbDirIn) {
    // IN transactions get copied into the SPI egress buffer.
    spi_device_copy_to_egress(kFlashBuffer, data, len);
  } else {
    // We set the total expected length for OUT transactions here.
    // The processing of the data packets happens in the main loop in response
    // to PAGE_PROGRAM opcodes.
    ctx->expected_len = len;
  }
}

rom_error_t dfu_transport_setupdata(dfu_ctx_t *ctx, usb_setup_data_t *setup) {
  OT_DISCARD(ctx);
  OT_DISCARD(setup);
  // We don't handle most of the standard setupdata requests over SPI.
  //
  // We do handle SetInterface/GetInterface in the main DFU handler; those
  // requests are used to set the ROM_EXT service that the client wants to
  // interact with.
  return kErrorUsbBadSetup;
}

void dfu_transport_result(dfu_ctx_t *ctx, rom_error_t result) {
  OT_DISCARD(ctx);
  uint32_t value = result;
  spi_device_copy_to_egress(kMailboxBuffer, &value, sizeof(value));
  spi_device_flash_status_clear();
}

rom_error_t rescue_protocol(boot_data_t *bootdata, boot_log_t *boot_log,
                            const owner_rescue_config_t *config) {
  dfu_ctx_t ctx = {
      .dfu_state = kDfuStateIdle,
      .dfu_error = kDfuErrOk,
  };
  dbg_printf("SPI-DFU rescue ready\r\n");
  rescue_state_init(&ctx.state, bootdata, boot_log, config);
  spi_device_init(
      /*log2_density=*/kRescueDensity, &kRescueSfdpTable,
      sizeof(kRescueSfdpTable));
  spi_device_enable_mailbox(kMailboxAddress);

  spi_device_cmd_t cmd;
  uint32_t length;
  while (true) {
    RETURN_IF_ERROR(rescue_inactivity(&ctx.state));
    rom_error_t result = spi_device_cmd_get(&cmd, /*blocking=*/false);
    switch (result) {
      case kErrorOk:
        break;
      case kErrorNoData:
        continue;
      default:
        return result;
    }
    switch (cmd.opcode) {
      case kSpiDeviceOpcodePageProgram: {
        if (cmd.address == kMailboxAddress) {
          usb_setup_data_t *setup = (usb_setup_data_t *)cmd.payload;
          dfu_protocol_handler(&ctx, 0, kUsbTransferFlagsSetupData, setup);
        } else {
          // Our payload buffer is 2K; truncate addresses.
          uint32_t offset = cmd.address & 0x7FF;
          if (offset + cmd.payload_byte_count > sizeof(ctx.state.data)) {
            // If the packet is too big, truncate to the size of the target
            // buffer.
            size_t excess =
                offset + cmd.payload_byte_count - sizeof(ctx.state.data);
            cmd.payload_byte_count -= excess;
          }
          memcpy(ctx.state.data + offset, cmd.payload, cmd.payload_byte_count);
          length = offset + cmd.payload_byte_count;
          if (length >= ctx.expected_len) {
            // Once we've recieved the entire data packet, ask the DFU state
            // machine to handle it.
            dfu_protocol_handler(&ctx, 0, kUsbTransferFlagsDone, &length);
            ctx.expected_len = 0;
          }
          spi_device_flash_status_clear();
        }
      } break;

      case kSpiDeviceOpcodeReset:
        rstmgr_reset();
        break;
      default:
        dfu_transport_result(&ctx, kErrorUsbBadSetup);
    }
  }
}
