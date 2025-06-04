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

const uint32_t rescue_type = kRescueProtocolUsbDfu;

static const usb_device_descriptor_t device_desc = {
    .length = (uint8_t)sizeof(usb_device_descriptor_t),
    .descriptor_type = kUsbDescTypeDevice,
    .bcd_usb = 0x0200,
    .device_class = 0,
    .device_sub_class = 0,
    .device_protocol = 0,
    .max_packet_size_0 = 64,
    .vendor = kUsbVendorGoogle,
    .product = kUsbProuctRomExt,
    .bcd_device = 0x100,
    .imanufacturer = 1,
    .iproduct = 2,
    .iserial_number = 3,
    .num_configurations = 1,
};

#define DFU_INTERFACE_DSCR(alt)                          \
  USB_INTERFACE_DSCR(/*inum=*/1, /*alt=*/alt, /*nep=*/0, \
                     /*class=*/kDfuDeviceClass,          \
                     /*subclass=*/kDfuDeviceSubClass,    \
                     /*protocol=*/kDfuDeviceProtocol, /*iint=*/4 + alt)

static const uint8_t config_desc[] = {
    USB_CFG_DSCR_HEAD(
        /*total_len=*/USB_CFG_DSCR_LEN + 6 * USB_INTERFACE_DSCR_LEN + 9,
        /*nint=*/1),
    DFU_INTERFACE_DSCR(0),
    DFU_INTERFACE_DSCR(1),
    DFU_INTERFACE_DSCR(2),
    DFU_INTERFACE_DSCR(3),
    DFU_INTERFACE_DSCR(4),
    DFU_INTERFACE_DSCR(5),

    /* DFU Functional Descriptor */
    /*bLength=*/kDfuFuncDescLen,
    /*bDescriptorType=*/kDfuFuncDescType,
    /*bmAttributes=*/kDfuFuncAttrCanDnLoad | kDfuFuncAttrCanUpLoad |
        kDfuFuncAttrManifestTolerant,
    /*wDetachTimeout*/ (uint8_t)kDfuFuncDetachTimeout,
    (uint8_t)(kDfuFuncDetachTimeout >> 8),
    /*wTransferSize*/ (uint8_t)kDfuTransferSize,
    (uint8_t)(kDfuTransferSize >> 8),
    /*bcdDFUVersion*/ kDfuMajorVersion,
    kDfuMinorVersion,
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
    NULL,
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

void dfu_transport_data(dfu_ctx_t *ctx, usb_dir_t dir, void *data, size_t len,
                        usb_transfer_flags_t flags) {
  OT_DISCARD(ctx);
  usb_ep_transfer((uint8_t)dir | 0, data, len, flags);
}

rom_error_t dfu_transport_setupdata(dfu_ctx_t *ctx, usb_setup_data_t *setup) {
  return usb_control_setupdata(&ctx->ep0, setup);
}

void dfu_transport_result(dfu_ctx_t *ctx, rom_error_t result) {
  OT_DISCARD(ctx);
  if (result != kErrorOk) {
    usb_ep_stall(0, true);
  }
}

rom_error_t rescue_protocol(boot_data_t *bootdata, boot_log_t *boot_log,
                            const owner_rescue_config_t *config) {
  set_serialnumber();
  dfu_ctx_t ctx = {
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
  rescue_state_init(&ctx.state, bootdata, boot_log, config);
  pinmux_init_usb();
  usb_init();
  usb_ep_init(0, kUsbEpTypeControl, 0x40, dfu_protocol_handler, &ctx);
  usb_enable(true);
  while (true) {
    usb_poll();
  }
  return kErrorOk;
}
