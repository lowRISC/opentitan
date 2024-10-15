// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/base/status.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/runtime/print.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"
#include "sw/device/silicon_creator/lib/drivers/flash_ctrl.h"

OTTF_DEFINE_TEST_CONFIG();

const char kBase64[] =
    "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/";

static void base64_encode(char *dest, const uint8_t *data, int32_t len) {
  for (int32_t i = 0; len > 0; i += 3, len -= 3) {
    // clang-format off
    uint32_t val = (uint32_t)(data[i] << 16 |
                              (len > 1 ? data[i + 1] << 8 : 0) |
                              (len > 2 ? data[i + 2] : 0));
    // clang-format on
    *dest++ = kBase64[(val >> 18) & 0x3f];
    *dest++ = kBase64[(val >> 12) & 0x3f];
    *dest++ = len > 1 ? kBase64[(val >> 6) & 0x3f] : '=';
    *dest++ = len > 2 ? kBase64[(val >> 0) & 0x3f] : '=';
  }
  *dest = '\0';
}

// TODO: when merging to master, use this function from
// //sw/device/silicon_creator/lib:cert.  It does not exist
// on `earlgrey_es_sival`.
static uint32_t cert_x509_asn1_decode_size_header(const uint8_t *header) {
  if (header[0] != 0x30 || header[1] != 0x82) {
    return 0;
  }
  return (((uint32_t)header[2]) << 8) + header[3] + 4 /* size of the header */;
}

static status_t print_cert(char *dest,
                           const flash_ctrl_info_page_t *info_page) {
  uint8_t data[2048];
  TRY(flash_ctrl_info_read(info_page, 0, sizeof(data) / sizeof(uint32_t),
                           data));

  uint32_t len = cert_x509_asn1_decode_size_header(data);
  base64_encode(dest, data, (int32_t)len);
  return OK_STATUS();
}

static status_t print_owner_block(char *dest,
                                  const flash_ctrl_info_page_t *info_page) {
  uint8_t data[2048];
  TRY(flash_ctrl_info_read(info_page, 0, sizeof(data) / sizeof(uint32_t),
                           data));
  base64_encode(dest, data, sizeof(data));
  return OK_STATUS();
}

static status_t print_certs(void) {
  char buf[3072];
  TRY(print_cert(buf, &kFlashCtrlInfoPageUdsCertificate));
  LOG_INFO("UDS: %s", buf);

  TRY(print_cert(buf, &kFlashCtrlInfoPageCdi0Certificate));
  LOG_INFO("CDI_0: %s", buf);

  TRY(print_cert(buf, &kFlashCtrlInfoPageCdi1Certificate));
  LOG_INFO("CDI_1: %s", buf);

  TRY(print_owner_block(buf, &kFlashCtrlInfoPageOwnerSlot0));
  LOG_INFO("OWNER_PAGE_0: %s", buf);

  TRY(print_owner_block(buf, &kFlashCtrlInfoPageOwnerSlot1));
  LOG_INFO("OWNER_PAGE_1: %s", buf);

  return OK_STATUS();
}

bool test_main(void) {
  status_t sts = print_certs();
  if (status_err(sts)) {
    LOG_ERROR("print_certs: %r", sts);
  }
  return status_ok(sts);
}
