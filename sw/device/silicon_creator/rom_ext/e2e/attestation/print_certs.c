// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include <stdint.h>

#include "sw/device/lib/base/crc32.h"
#include "sw/device/lib/base/macros.h"
#include "sw/device/lib/base/memory.h"
#include "sw/device/lib/base/status.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/runtime/print.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"
#include "sw/device/silicon_creator/lib/base/static_dice_mldsa_cdi.h"
#include "sw/device/silicon_creator/lib/base/util.h"
#include "sw/device/silicon_creator/lib/cert/dice_storage.h"
#include "sw/device/silicon_creator/lib/cert/ram_msg.h"
#include "sw/device/silicon_creator/lib/drivers/flash_ctrl.h"
#include "sw/device/silicon_creator/lib/drivers/retention_sram.h"
#include "sw/device/silicon_creator/lib/drivers/rstmgr.h"
#include "sw/device/silicon_creator/lib/error.h"
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
    perso_tlv_cert_obj_view_t obj = {0};
    rom_error_t err = perso_tlv_get_cert_obj_view(data + offset, len, &obj);
    if (err != kErrorOk) {
      break;
    }
    base64_encode(dest, obj.cert_body_p, (int32_t)obj.cert_body_size);
    LOG_INFO("%s type=%d sz=%d/%d", obj.name, obj.obj_type, obj.cert_body_size,
             obj.obj_size);
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
#ifndef POST_PROVISIONING_TESTS
  // On non-silicon targets, the factory certs pages will not be provisioned,
  // and it is not updated by the ROM_EXT if it is not provisioned. This will
  // trigger an ECC error when trying to read a page that has scrambling setup
  // by the ROM_EXT but is not erased after.
  if (kDeviceType == kDeviceSilicon) {
    TRY(print_cert(buf, &kFlashCtrlInfoPageFactoryCerts));
  }
#else   // POST_PROVISIONING_TESTS
  // If this test is being run just after running a provisioning test which
  // wrote the UDS certificate to FACTORY INFO page, read and print the UDS
  // cert. Note that for FPGAs the bitstream must not be cleared after running
  // the provisioning test
  TRY(print_cert(buf, &kFlashCtrlInfoPageFactoryCerts));
#endif  // POST_PROVISIONING_TESTS

  TRY(print_cert(buf, &kFlashCtrlInfoPageDiceCerts));

  // Print owner information.
  TRY(print_owner_block(buf, &kFlashCtrlInfoPageOwnerSlot0));
  LOG_INFO("OWNER_PAGE_0: %s", buf);

  TRY(print_owner_block(buf, &kFlashCtrlInfoPageOwnerSlot1));
  LOG_INFO("OWNER_PAGE_1: %s", buf);

  return OK_STATUS();
}

const flash_ctrl_info_page_t *const mldsa_endorsed_cert_pages[4] = {
    &kFlashCtrlInfoPageOwnerReserved0,
    &kFlashCtrlInfoPageOwnerReserved1,
    &kFlashCtrlInfoPageOwnerReserved2,
    &kFlashCtrlInfoPageOwnerReserved3,
};
static uint8_t
    endorsed_uds_mldsa_cert[FLASH_CTRL_PARAM_BYTES_PER_PAGE *
                            ARRAYSIZE(
                                mldsa_endorsed_cert_pages)] OT_WORD_ALIGNED;

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
  dice_storage_slot_v1_t cdi0_slot = {.bank_idx = 0};
  dice_storage_slot_v1_t cdi1_slot = {.bank_idx = 1};
  uint32_t flash_cdi0 = (uint32_t)dice_storage_slot_v1_data(&cdi0_slot);
  uint32_t flash_cdi1 = (uint32_t)dice_storage_slot_v1_data(&cdi1_slot);
  uint32_t ram_cdi0 = (uint32_t)static_dice_mldsa_cdi.cdi_0_cert;
  uint32_t ram_cdi1 = (uint32_t)static_dice_mldsa_cdi.cdi_1_cert;

  bool flash_storage_mode = res->mldsa_cdi0_cert == flash_cdi0;
  LOG_INFO("DICE cert storage mode: %s", flash_storage_mode ? "Flash" : "RAM");

  uint32_t expected_cdi0 = flash_storage_mode ? flash_cdi0 : ram_cdi0;
  uint32_t expected_cdi1 = flash_storage_mode ? flash_cdi1 : ram_cdi1;

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

  if (flash_storage_mode) {
    perso_tlv_cert_obj_view_t cdi0_obj = {0};
    perso_tlv_cert_obj_view_t cdi1_obj = {0};
    uint8_t *slot0_hdr = (uint8_t *)dice_storage_slot_v1_header(&cdi0_slot);
    uint8_t *slot1_hdr = (uint8_t *)dice_storage_slot_v1_header(&cdi1_slot);
    size_t slot_max_len =
        (uintptr_t)_rom_ext_size - (uintptr_t)_rom_ext_protected_size;

    rom_error_t err =
        perso_tlv_get_cert_obj_view(slot0_hdr, slot_max_len, &cdi0_obj);
    if (err != kErrorOk) {
      LOG_ERROR("Failed to parse CDI_0 TLV from flash: 0x%08x", err);
      return INTERNAL(8);
    }
    LOG_INFO("%s type=%d sz=%d/%d", cdi0_obj.name, cdi0_obj.obj_type,
             cdi0_obj.cert_body_size, cdi0_obj.obj_size);

    err = perso_tlv_get_cert_obj_view(slot1_hdr, slot_max_len, &cdi1_obj);
    if (err != kErrorOk) {
      LOG_ERROR("Failed to parse CDI_1 TLV from flash: 0x%08x", err);
      return INTERNAL(9);
    }
    LOG_INFO("%s type=%d sz=%d/%d", cdi1_obj.name, cdi1_obj.obj_type,
             cdi1_obj.cert_body_size, cdi1_obj.obj_size);

    if (cdi0_obj.obj_type != kPersoObjectTypeX509Cert ||
        cdi0_obj.cert_body_p != (uint8_t *)res->mldsa_cdi0_cert ||
        cdi0_obj.cert_body_size != res->mldsa_cdi0_cert_len) {
      LOG_ERROR("CDI_0 TLV body does not match handover response");
      return INTERNAL(10);
    }

    if (cdi1_obj.obj_type != kPersoObjectTypeX509Cert ||
        cdi1_obj.cert_body_p != (uint8_t *)res->mldsa_cdi1_cert ||
        cdi1_obj.cert_body_size != res->mldsa_cdi1_cert_len) {
      LOG_ERROR("CDI_1 TLV body does not match handover response");
      return INTERNAL(11);
    }
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

#ifdef POST_PROVISIONING_TESTS
  for (size_t i = 0; i < ARRAYSIZE(mldsa_endorsed_cert_pages); i++) {
    flash_ctrl_cfg_t cfg = {
        .scrambling = kMultiBitBool4True,
        .ecc = kMultiBitBool4True,
        .he = kMultiBitBool4False,
    };
    flash_ctrl_info_cfg_set(mldsa_endorsed_cert_pages[i], cfg);
    const flash_ctrl_perms_t perms = {
        .read = kMultiBitBool4True,
        .write = kMultiBitBool4True,
        .erase = kMultiBitBool4True,
    };
    flash_ctrl_info_perms_set(mldsa_endorsed_cert_pages[i], perms);
    TRY(flash_ctrl_info_read(
        mldsa_endorsed_cert_pages[i], /*offset=*/0,
        util_size_to_words(FLASH_CTRL_PARAM_BYTES_PER_PAGE),
        (uint8_t *)endorsed_uds_mldsa_cert +
            i * FLASH_CTRL_PARAM_BYTES_PER_PAGE));
  }

  perso_tlv_cert_obj_view_t uds_mldsa_obj = {0};
  rom_error_t err = perso_tlv_get_cert_obj_view(
      endorsed_uds_mldsa_cert, sizeof(endorsed_uds_mldsa_cert), &uds_mldsa_obj);
  if (err != kErrorOk) {
    LOG_ERROR(
        "Failed to parse UDS ML-DSA 44 TLV from flash: 0x%08x. Maybe it is not "
        "present?",
        err);
  } else {
    LOG_INFO("UDS MLDSA cert size: %u", uds_mldsa_obj.cert_body_size);
    TRY_CHECK(uds_mldsa_obj.cert_body_size <= INT32_MAX);
    base64_encode(buf, uds_mldsa_obj.cert_body_p,
                  (int32_t)uds_mldsa_obj.cert_body_size);
    LOG_INFO("UDS_MLDSA_CERT: %s", buf);
  }
#endif  // POST_PROVISIONING_TESTS

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
