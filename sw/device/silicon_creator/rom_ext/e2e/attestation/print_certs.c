// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/base/crc32.h"
#include "sw/device/lib/base/memory.h"
#include "sw/device/lib/base/status.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/runtime/print.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"
#include "sw/device/silicon_creator/lib/base/static_dice_mldsa_cdi.h"
#include "sw/device/silicon_creator/lib/cert/dice_storage.h"
#include "sw/device/silicon_creator/lib/cert/ram_msg.h"
#include "sw/device/silicon_creator/lib/drivers/flash_ctrl.h"
#include "sw/device/silicon_creator/lib/drivers/retention_sram.h"
#include "sw/device/silicon_creator/lib/drivers/rstmgr.h"
#include "sw/device/silicon_creator/lib/manifest_def.h"
#include "sw/device/silicon_creator/manuf/base/perso_tlv_data.h"

static char buf[12288];

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

static status_t print_cert(char *dest,
                           const flash_ctrl_info_page_t *info_page) {
  uint8_t data[2048];
  TRY(flash_ctrl_info_read(info_page, 0, sizeof(data) / sizeof(uint32_t),
                           data));

  uint32_t offset = 0;
  size_t len = sizeof(data);
  while (true) {
    perso_tlv_cert_obj_t obj = {0};
    rom_error_t err =
        perso_tlv_get_cert_obj(data + offset, len, kPersoBlobVersionV0, &obj);
    if (err != kErrorOk) {
      break;
    }
    base64_encode(dest, obj.cert_body_p, (int32_t)obj.cert_body_size);
    LOG_INFO("%s type=%d sz=%d", obj.name, obj.obj_type, obj.obj_size);
    LOG_INFO("%s: %s", obj.name, dest);
    offset += (obj.obj_size + 7) & ~7u;
    len -= obj.obj_size;
  }
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
  // Print certificates.
  // TODO: print factory certs on FPGA;
  // On non-silicon targets, the factory certs pages will not be provisioned,
  // and it is not updated by the ROM_EXT if it is not provisioned. This will
  // trigger an ECC error when trying to read a page that has scrambling setup
  // by the ROM_EXT but is not erased after.
  if (kDeviceType == kDeviceSilicon) {
    TRY(print_cert(buf, &kFlashCtrlInfoPageFactoryCerts));
  }
  TRY(print_cert(buf, &kFlashCtrlInfoPageDiceCerts));

  // Print owner information.
  TRY(print_owner_block(buf, &kFlashCtrlInfoPageOwnerSlot0));
  LOG_INFO("OWNER_PAGE_0: %s", buf);

  TRY(print_owner_block(buf, &kFlashCtrlInfoPageOwnerSlot1));
  LOG_INFO("OWNER_PAGE_1: %s", buf);

  return OK_STATUS();
}

static status_t verify_handover(void) {
  retention_sram_t *retram = retention_sram_get();
  dice_cert_gen_msg_t *msg = &retram->creator.dice_cert_gen;
  uint32_t type = msg->hdr.type;

  // ROM_EXT detection: if type is neither Response nor Ids, we are not running
  // ML-DSA ROM_EXT.
  if (type != kDiceCertGenResponse && type != kDiceCertGenIds) {
    LOG_INFO("ML-DSA DICE certs not supported by ROM_EXT; skipping ML-DSA.");
    return OK_STATUS();
  }

  // Handle IDs-only response (Cold Boot)
  if (type == kDiceCertGenIds) {
    LOG_INFO(
        "Cold boot: ML-DSA Key IDs are present, but certificates are not "
        "generated yet.");

    uint64_t cdi0_id = read_64(msg->ids.mldsa_cdi0_id);
    uint64_t cdi1_id = read_64(msg->ids.mldsa_cdi1_id);

    LOG_INFO("CDI_0 ML-DSA Key ID: 0x%08x%08x", (uint32_t)(cdi0_id >> 32),
             (uint32_t)cdi0_id);
    LOG_INFO("CDI_1 ML-DSA Key ID: 0x%08x%08x", (uint32_t)(cdi1_id >> 32),
             (uint32_t)cdi1_id);

    // Set request type.
    LOG_INFO("Requesting cert generation and rebooting...");
    msg->hdr.type = kDiceCertGenRequest;
    msg->hdr.version = 0;

    // Trigger warm reboot.
    rstmgr_reset();

    // We should never reach here.
    return INTERNAL(1);
  }

  // Handle Full Response (Warm Boot)
  LOG_INFO(
      "Warm boot: ML-DSA certificates and Key IDs are present in Retention "
      "RAM!");

  dice_cert_gen_res_t *res = &msg->res;

  // Verify CRC32.
  uint32_t expected_crc = res->crc32;
  uint32_t calculated_crc =
      crc32(res, sizeof(dice_cert_gen_res_t) - sizeof(uint32_t));
  if (calculated_crc != expected_crc) {
    LOG_ERROR("Handover CRC32 mismatch! Expected 0x%08x, got 0x%08x",
              expected_crc, calculated_crc);
    return INTERNAL(2);
  }
  LOG_INFO("Handover CRC32 verified successfully: 0x%08x", calculated_crc);

  uint64_t cdi0_id = read_64(res->mldsa_cdi0_id);
  uint64_t cdi1_id = read_64(res->mldsa_cdi1_id);

  LOG_INFO("CDI_0 ML-DSA Key ID: 0x%08x%08x", (uint32_t)(cdi0_id >> 32),
           (uint32_t)cdi0_id);
  LOG_INFO("CDI_1 ML-DSA Key ID: 0x%08x%08x", (uint32_t)(cdi1_id >> 32),
           (uint32_t)cdi1_id);

  // Print handed over pointers and sizes.
  LOG_INFO("Handed over UDS pub key at 0x%08x (size %d)", res->mldsa_uds_pub,
           res->mldsa_uds_pub_len);
  LOG_INFO("Handed over CDI_0 cert at 0x%08x (size %d)", res->mldsa_cdi0_cert,
           res->mldsa_cdi0_cert_len);
  LOG_INFO("Handed over CDI_1 cert at 0x%08x (size %d)", res->mldsa_cdi1_cert,
           res->mldsa_cdi1_cert_len);

  // Verify pointers match static_dice_mldsa_cdi buffer locations.
  if (res->mldsa_uds_pub != (uint32_t)static_dice_mldsa_cdi.uds_pub) {
    LOG_ERROR(
        "Handed over UDS pub key pointer mismatch! Expected: 0x%08x, Got: "
        "0x%08x",
        (uint32_t)static_dice_mldsa_cdi.uds_pub, res->mldsa_uds_pub);
    return INTERNAL(5);
  }
  bool flash_storage_mode =
      manifest_def_get()->dice_cert_storage_mode == kDiceCertMldsaOnFlash;
  LOG_INFO("DICE cert storage mode: %s", flash_storage_mode ? "Flash" : "RAM");

  uint32_t expected_cdi0 = 0;
  uint32_t expected_cdi1 = 0;
  if (flash_storage_mode) {
    dice_storage_slot_v1_t cdi0_slot = {.bank_idx = 0};
    dice_storage_slot_v1_t cdi1_slot = {.bank_idx = 1};
    expected_cdi0 = (uint32_t)dice_storage_slot_v1_data(&cdi0_slot);
    expected_cdi1 = (uint32_t)dice_storage_slot_v1_data(&cdi1_slot);
  } else {
    expected_cdi0 = (uint32_t)static_dice_mldsa_cdi.cdi_0_cert;
    expected_cdi1 = (uint32_t)static_dice_mldsa_cdi.cdi_1_cert;
  }

  if (res->mldsa_cdi0_cert != expected_cdi0) {
    LOG_ERROR(
        "Handed over CDI_0 cert pointer mismatch! Expected: 0x%08x, Got: "
        "0x%08x",
        expected_cdi0, res->mldsa_cdi0_cert);
    return INTERNAL(6);
  }
  if (res->mldsa_cdi1_cert != expected_cdi1) {
    LOG_ERROR(
        "Handed over CDI_1 cert pointer mismatch! Expected: 0x%08x, Got: "
        "0x%08x",
        expected_cdi1, res->mldsa_cdi1_cert);
    return INTERNAL(7);
  }

  // Read and encode certificates.
  base64_encode(buf, (const uint8_t *)res->mldsa_uds_pub,
                (int32_t)res->mldsa_uds_pub_len);
  LOG_INFO("UDS_MLDSA: %s", buf);

  base64_encode(buf, (const uint8_t *)res->mldsa_cdi0_cert,
                (int32_t)res->mldsa_cdi0_cert_len);
  LOG_INFO("CDI_0_MLDSA: %s", buf);

  base64_encode(buf, (const uint8_t *)res->mldsa_cdi1_cert,
                (int32_t)res->mldsa_cdi1_cert_len);
  LOG_INFO("CDI_1_MLDSA: %s", buf);

  msg->hdr.type = 0;

  return OK_STATUS();
}

bool test_main(void) {
  status_t sts = verify_handover();
  if (status_err(sts)) {
    LOG_ERROR("verify_handover failed: %r", sts);
    return false;
  }

  sts = print_certs();
  if (status_err(sts)) {
    LOG_ERROR("print_certs: %r", sts);
  }
  return status_ok(sts);
}
