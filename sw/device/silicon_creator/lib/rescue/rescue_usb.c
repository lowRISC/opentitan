// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include <stdbool.h>
#include <stdint.h>

#include "sw/device/lib/arch/device.h"
#include "sw/device/lib/base/macros.h"
#include "sw/device/silicon_creator/lib/boot_data.h"
#include "sw/device/silicon_creator/lib/dbg_print.h"
#include "sw/device/silicon_creator/lib/drivers/lifecycle.h"
#include "sw/device/silicon_creator/lib/drivers/pinmux.h"
#include "sw/device/silicon_creator/lib/drivers/rstmgr.h"
#include "sw/device/silicon_creator/lib/drivers/usb.h"
#include "sw/device/silicon_creator/lib/error.h"
#include "sw/device/silicon_creator/lib/rescue/dfu.h"
#include "sw/device/silicon_creator/lib/rescue/rescue.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

static const usb_device_descriptor_t device_desc = {
    .length = 18,
    .descriptor_type = 1,
    .bcd_usb = 0x0200,
    .device_class = 0,
    .device_sub_class = 0,
    .device_protocol = 0,
    .max_packet_size_0 = 64,
    // TODO(cfrantz): Does lowRISC have a USB vendor ID?
    .vendor = 0x18d1,
    .product = 0x503a,
    .bcd_device = 0x100,
    .imanufacturer = 1,
    .iproduct = 2,
    .iserial_number = 3,
    .num_configurations = 1,
};

#define DFU_INTERFACE_DSCR(alt)                                          \
  USB_INTERFACE_DSCR(/*inum=*/1, /*alt=*/alt, /*nep=*/0, /*class=*/0xFE, \
                     /*subclass=*/0x01, /*protocol=*/2, /*iint=*/4 + alt)

static const uint8_t config_desc[] = {
    USB_CFG_DSCR_HEAD(
        /*total_len=*/USB_CFG_DSCR_LEN + 6 * USB_INTERFACE_DSCR_LEN + 9,
        /*nint=*/1),
    DFU_INTERFACE_DSCR(0), DFU_INTERFACE_DSCR(1), DFU_INTERFACE_DSCR(2),
    DFU_INTERFACE_DSCR(3), DFU_INTERFACE_DSCR(4), DFU_INTERFACE_DSCR(5),

    /* DFU Functional Descriptor */
    /*bLength=*/0x09,
    /*bDescriptorType=*/0x21,
    /*bmAttributes=*/0x07,  // will_detach=no, mftol=yes, upload=yes, dnload=yes
    /*wDetachTimeout*/ 0x00, 0x80,  // 32768ms
    /*wTransferSize*/ 0x00, 0x08,   // 2K
    /*bcdDFUVersion*/ 0x01, 0x01,   // 1.1
};

static const char lang_id[] = {
    /* bLength=*/4,
    /* bDescriptorType=*/3,
    /* bString=*/0x09,
    0x04,
};

// clang-format off
static const char str_vendor[] = { USB_STRING_DSCR('G','o','o','g','l','e'), };
static const char str_opentitan[] = { USB_STRING_DSCR('O','p','e','n','T','i','t','a','n'), };
static const char str_resq[] = { USB_STRING_DSCR('R','e','s','c','u','e') };
static const char str_resb[] = { USB_STRING_DSCR('R','e','s','c','u','e',' ','S','l','o','t','B')};
static const char str_otid[] = { USB_STRING_DSCR('D','e','v','i','c','e','I','D') };
static const char str_blog[] = { USB_STRING_DSCR('B','o','o','t','L','o','g') };
static const char str_bsvc[] = { USB_STRING_DSCR('B','o','o','t','S','e','r','v','i','c','e','s') };
static const char str_ownr[] = { USB_STRING_DSCR('O','w','n','e','r','s','h','i','p') };

// Located in RAM so we can fill in the OpenTitan device ID.
static char str_serialnumber[2 + 32];

static const char *string_desc[] = {
    lang_id,
    str_vendor,
    str_opentitan,
    str_serialnumber,
    str_resq,
    str_resb,
    str_otid,
    str_blog,
    str_bsvc,
    str_ownr,
};
// clang-format on

// TODO: make sure we report this in the proper order.
static void set_serialnumber(void) {
  lifecycle_device_id_t dev;
  lifecycle_device_id_get(&dev);
  const char hex[] = "0123456789ABCDEF";

  char *sn = str_serialnumber;
  *sn++ = 2 + 32;
  *sn++ = 3;
  for (size_t w = 1; w < 3; ++w) {
    uint8_t byte = (uint8_t)(dev.device_id[w] >> 24);
    *sn++ = hex[byte >> 4];
    *sn++ = 0;
    *sn++ = hex[byte & 15];
    *sn++ = 0;
    byte = (uint8_t)(dev.device_id[w] >> 16);
    *sn++ = hex[byte >> 4];
    *sn++ = 0;
    *sn++ = hex[byte & 15];
    *sn++ = 0;
    byte = (uint8_t)(dev.device_id[w] >> 8);
    *sn++ = hex[byte >> 4];
    *sn++ = 0;
    *sn++ = hex[byte & 15];
    *sn++ = 0;
    byte = (uint8_t)(dev.device_id[w] >> 0);
    *sn++ = hex[byte >> 4];
    *sn++ = 0;
    *sn++ = hex[byte & 15];
    *sn++ = 0;
  }
}

void dfu_transport_data(size_t ep, void *data, size_t len,
                        usb_transfer_flags_t flags) {
  usb_ep_transfer(ep, data, len, flags);
}

rom_error_t dfu_transport_setupdata(usb_control_ctx_t *ctx,
                                    usb_setup_data_t *setup) {
  return usb_control_setupdata(ctx, setup);
}

void dfu_transport_result(rom_error_t result) {
  if (result != kErrorOk) {
    usb_ep_stall(0, true);
  }
}

rom_error_t rescue_protocol(boot_data_t *bootdata,
                            const owner_rescue_config_t *config) {
  set_serialnumber();
  dfu_ctx_t ctx = {
      .bootdata = bootdata,
      .ep0 =
          {
              .device_desc = &device_desc,
              .config_desc = config_desc,
              .string_desc = string_desc,
          },
      .dfu_state = kDfuStateIdle,
      .dfu_error = kDfuErrOk,
  };
  dbg_printf("USB-DFU rescue ready\r\n");
  rescue_state_init(&ctx.state, config);
  pinmux_init_usb();
  usb_init();
  usb_ep_init(0, kUsbEndpointTypeControl, 0x40, dfu_protocol_handler, &ctx);
  usb_enable(true);
  while (true) {
    usb_poll();
  }
  return kErrorOk;
}
