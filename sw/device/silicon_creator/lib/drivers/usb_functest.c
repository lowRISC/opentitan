// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include <stdbool.h>
#include <stdint.h>

#include "sw/device/lib/arch/device.h"
#include "sw/device/lib/base/macros.h"
#include "sw/device/lib/runtime/print.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"
#include "sw/device/silicon_creator/lib/drivers/hmac.h"
#include "sw/device/silicon_creator/lib/drivers/lifecycle.h"
#include "sw/device/silicon_creator/lib/drivers/pinmux.h"
#include "sw/device/silicon_creator/lib/drivers/rnd.h"
#include "sw/device/silicon_creator/lib/drivers/usb.h"
#include "sw/device/silicon_creator/lib/error.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

OTTF_DEFINE_TEST_CONFIG();

const usb_device_descriptor_t device_desc = {
    .length = 18,
    .descriptor_type = 1,
    .bcd_usb = 0x0200,
    .device_class = 0xFF,
    .device_sub_class = 0xFF,
    .device_protocol = 0xFF,
    .max_packet_size_0 = 64,
    .vendor = 0x18d1,
    .product = 0x503a,
    .bcd_device = 0x100,
    .imanufacturer = 1,
    .iproduct = 2,
    .iserial_number = 3,
    .num_configurations = 1,
};

const uint8_t config_desc[] = {
    USB_CFG_DSCR_HEAD(
        /*total_len=*/USB_CFG_DSCR_LEN + USB_INTERFACE_DSCR_LEN +
            2 * USB_EP_DSCR_LEN,
        /*nint=*/1),
    USB_INTERFACE_DSCR(
        /*inum=*/1,
        /*alt=*/0,
        /*nep=*/2,
        /*class=*/0xFF,
        /*subclass=*/0xFF,
        /*protocol=*/1,
        /*iint=*/0),
    USB_BULK_EP_DSCR(
        /*in=*/false,
        /*ep=*/1,
        /*maxsize=*/64,
        /*interval=*/0),
    USB_BULK_EP_DSCR(
        /*in=*/true,
        /*ep=*/2,
        /*maxsize=*/64,
        /*interval=*/0),
};

const char lang_id[] = {
    /* bLength=*/4,
    /* bDescriptorType=*/3,
    /* bString=*/0x09,
    0x04,
};

const char str_vendor[] = {
    USB_STRING_DSCR('G', 'o', 'o', 'g', 'l', 'e'),
};

const char str_opentitan[] = {
    USB_STRING_DSCR('O', 'p', 'e', 'n', 'T', 'i', 't', 'a', 'n'),
};

char str_serialnumber[2 + 32];

const char *string_desc[] = {
    lang_id, str_vendor, str_opentitan, str_serialnumber, NULL,
};

usb_control_ctx_t ep0 = {
    .device_desc = &device_desc,
    .config_desc = config_desc,
    .string_desc = string_desc,
};

uint32_t work_buffer[16384];
uint32_t test_exit;

typedef enum test_req {
  kTestReqRandomize = 1,
  kTestReqDigest = 2,
  kTestReqBulkIn = 3,
  kTestReqBulkOut = 4,
  kTestReqExit = 5,
} test_req_t;

void set_serialnumber(void) {
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

rom_error_t my_control(usb_setup_data_t *setup) {
  switch (setup->request) {
    case kTestReqRandomize:
      base_printf("Randomize\r\n");
      for (size_t i = 0; i < ARRAYSIZE(work_buffer); ++i) {
        work_buffer[i] = rnd_uint32();
      }
      usb_ep_transfer(kUsbDirIn | 0, NULL, 0, 0);
      break;

    case kTestReqDigest: {
      base_printf("Digest sz=%u\r\n", (size_t)setup->value + 1);
      hmac_digest_t digest;
      hmac_sha256_configure(true);
      hmac_sha256_start();
      hmac_sha256_update(work_buffer, (size_t)setup->value + 1);
      hmac_sha256_process();
      hmac_sha256_final(&digest);
      usb_ep_transfer(kUsbDirIn | 0, &digest, sizeof(digest), 0);
      break;
    }
    case kTestReqBulkIn: {
      size_t length = (size_t)setup->value + 1;
      uint8_t ep = (uint8_t)setup->index;
      base_printf("BulkIn ep=%u sz=%u\r\n", setup->index, length);
      usb_ep_transfer(
          kUsbDirIn | ep, work_buffer, length,
          (length < sizeof(work_buffer) ? kUsbTransferFlagsShortIn : 0));
      usb_ep_transfer(kUsbDirIn | 0, NULL, 0, 0);
      break;
    }
    case kTestReqBulkOut: {
      size_t length = (size_t)setup->value + 1;
      uint8_t ep = (uint8_t)setup->index;
      base_printf("BulkOut ep=%u sz=%u\r\n", setup->index, length);
      usb_ep_transfer(ep, work_buffer, length, 0);
      usb_ep_transfer(kUsbDirIn | 0, NULL, 0, 0);
      break;
    }
    case kTestReqExit:
      base_printf("Exit\r\n");
      test_exit = 1;
      usb_ep_transfer(kUsbDirIn | 0, NULL, 0, 0);
      break;
    default:
      return kErrorUsbBadSetup;
  }
  return kErrorOk;
}

void handler(void *ctx, uint8_t ep, usb_transfer_flags_t flags, void *data) {
  OT_DISCARD(ctx);
  if (flags & kUsbTransferFlagsSetupData) {
    usb_setup_data_t *setup = (usb_setup_data_t *)data;
    base_printf(
        "SETUPDATA: type=%02x req=%02x value=%04x index=%04x len=%04x\r\n",
        setup->request_type, setup->request, setup->value, setup->index,
        setup->length);
    rom_error_t error;
    if ((setup->request_type & kUsbReqTypeTypeMask) == kUsbReqTypeVendor) {
      error = my_control(setup);
    } else {
      error = usb_control_setupdata(&ep0, setup);
    }
    if (ep0.flags & kUsbControlFlagsPendingConfig) {
      ep0.flags &= ~(unsigned)kUsbControlFlagsPendingConfig;
      ep0.configuration = ep0.next.configuration;
      LOG_INFO("set_configuration %u", ep0.configuration);
      usb_ep_transfer(kUsbDirIn | 0, NULL, 0, 0);
    }
    if (error != kErrorOk) {
      usb_ep_stall(0, true);
    }
  }
  if (flags & kUsbTransferFlagsDone) {
    if (ep0.flags & kUsbControlFlagsPendingAddress) {
      ep0.flags &= ~(unsigned)kUsbControlFlagsPendingAddress;
      ep0.device_address = ep0.next.device_address;
      usb_set_address(ep0.device_address);
      LOG_INFO("set_addr %u", ep0.device_address);
    }

    if (test_exit == 1) {
      test_exit = 2;
    }
  }
  if (ep != 0) {
    int length = (flags & kUsbTransferFlagsDone) ? *(int *)data : -1;
    base_printf("Event on EP%u: flags=%08x length=%d\r\n", ep, flags, length);
  }
}

rom_error_t usb_test(void) {
  set_serialnumber();
  usb_init();
  usb_ep_init(0x00, kUsbEpTypeControl, 0x40, handler, NULL);
  usb_ep_init(0x01, kUsbEpTypeBulk, 0x40, handler, NULL);
  usb_ep_init(0x82, kUsbEpTypeBulk, 0x40, handler, NULL);
  usb_enable(true);
  LOG_INFO("usb ready");
  while (test_exit != 2) {
    usb_poll();
  }
  return kErrorOk;
}

bool test_main(void) {
  pinmux_init_usb();
  status_t result = OK_STATUS();
  EXECUTE_TEST(result, usb_test);
  return status_ok(result);
}
