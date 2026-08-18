// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include <assert.h>
#include <stddef.h>
#include <string.h>

#include "sw/device/lib/base/macros.h"
#include "sw/device/lib/base/status.h"
#include "sw/device/lib/testing/json/provisioning_data.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/silicon_creator/lib/base/util.h"
#include "sw/device/silicon_creator/lib/drivers/flash_ctrl.h"
#include "sw/device/silicon_creator/lib/drivers/hmac.h"
#include "sw/device/silicon_creator/lib/error.h"
#include "sw/device/silicon_creator/manuf/base/perso_tlv_data.h"
#include "sw/device/silicon_creator/manuf/base/personalize_ext.h"

#include "flash_ctrl_regs.h"  // Generated.

status_t personalize_extension_pre_cert_endorse(
    personalize_extension_pre_endorse_t *pre_params) {
  OT_DISCARD(pre_params);
  return OK_STATUS();
}

static size_t perso_blob_body_left(const perso_blob_t *blob, size_t next_free) {
  if (next_free > sizeof(blob->body)) {
    return 0;
  }

  return (sizeof(blob->body) - next_free);
}

static status_t extract_mldsa_uds_cert(const perso_blob_t *blob_from_host,
                                       perso_tlv_cert_obj_view_t *block) {
  size_t num_objs = blob_from_host->num_objs;
  size_t next_free = 0;

  while (num_objs > 0) {
    if (next_free > sizeof(blob_from_host->body)) {
      return INTERNAL();
    }
    rom_error_t err = perso_tlv_get_cert_obj_view(
        blob_from_host->body + next_free,
        perso_blob_body_left(blob_from_host, next_free), block);
    switch (err) {
      case kErrorOk:
        if (memcmp("PQ_UDS_44", block->name, sizeof("PQ_UDS_44")) == 0) {
          return OK_STATUS();
        }
        // Not the cert we are looking for
        next_free += block->obj_size;
        num_objs--;
        continue;
      case kErrorPersoTlvCertObjNotFound: {
        // The object found is not a certificate. Skip to next perso LTV object.
        const uint32_t obj_size = perso_tlv_object_size(
            blob_from_host->body + next_free,
            perso_blob_body_left(blob_from_host, next_free));
        if (obj_size == 0) {
          // Unlikely scenario. But return error since num_objs is decremented
          // but next_free is not incremented
          return INTERNAL();
        }
        next_free += obj_size;
        num_objs--;
        continue;
      }
      default:
        return INTERNAL();
    }
  }
  return NOT_FOUND();
}

static size_t min(size_t a, size_t b) { return (a < b) ? a : b; }

// NOTE: These pages are already erased in `ft_personalize.c` in
// `erase_owner_info_pages`. That functions sets the permissions as well. So
// they can be directly written to here
const flash_ctrl_info_page_t *const mldsa_endorsed_cert_pages[4] = {
    &kFlashCtrlInfoPageOwnerReserved0,
    &kFlashCtrlInfoPageOwnerReserved1,
    &kFlashCtrlInfoPageOwnerReserved2,
    &kFlashCtrlInfoPageOwnerReserved3,
};

enum {
  // Not enough space in `.bss` to read full page, so using smaller buffer with
  // more read operations
  kScratchCertBufferSize = 1024,
};

typedef struct cert_scratch_buffer {
  uint8_t buffer[kScratchCertBufferSize];
} __attribute__((aligned(4))) cert_scratch_buffer_t;

static status_t write_certificate(cert_scratch_buffer_t *cert_buffer,
                                  const perso_tlv_cert_obj_view_t *cert) {
  // Write MLDSA UDS cert to internal flash pages in parts
  for (size_t i = 0; i < ARRAYSIZE(mldsa_endorsed_cert_pages); i++) {
    static_assert(
        (FLASH_CTRL_PARAM_BYTES_PER_PAGE % sizeof(cert_buffer->buffer)) == 0,
        "Following logic to write data to flash info page expects that flash "
        "info page size is a multiple of the scratch buffer size");
    for (size_t j = 0;
         j < (FLASH_CTRL_PARAM_BYTES_PER_PAGE / sizeof(cert_buffer->buffer));
         j++) {
      const size_t obj_offset = (i * FLASH_CTRL_PARAM_BYTES_PER_PAGE) +
                                (j * sizeof(cert_buffer->buffer));
      if (cert->obj_size > obj_offset) {
        const size_t obj_size_to_write =
            min(cert->obj_size - obj_offset, sizeof(cert_buffer->buffer));
        memset(cert_buffer->buffer, 0, sizeof(cert_buffer->buffer));
        memcpy(cert_buffer->buffer, (uint8_t *)cert->obj_p + obj_offset,
               obj_size_to_write);
        static_assert(alignof(cert_scratch_buffer_t) % 4 == 0,
                      "Use word aligned buffer for writing to INFO flash");
        TRY(flash_ctrl_info_write(
            mldsa_endorsed_cert_pages[i],
            /*page_offset=*/j * sizeof(cert_buffer->buffer),
            util_size_to_words(obj_size_to_write), cert_buffer->buffer));
      }
    }
  }
  return OK_STATUS();
}

static status_t hash_certificate(
    cert_scratch_buffer_t *cert_buffer,
    const perso_tlv_cert_obj_view_t *expected_cert) {
  memset(cert_buffer->buffer, 0, sizeof(cert_buffer->buffer));

  static_assert(ARRAYSIZE(mldsa_endorsed_cert_pages) > 0,
                "expect at least one page to read header");

  // Read first 16 bytes of the certificate perso LTV object to determine size.
  static_assert(
      sizeof(cert_buffer->buffer) >= 16,
      "The logic below needs the scratch buffer to be at least 16 bytes");
  TRY(flash_ctrl_info_read(mldsa_endorsed_cert_pages[0], /*offset=*/0,
                           util_size_to_words(16), cert_buffer->buffer));
  const uint32_t obj_size = perso_tlv_object_size(cert_buffer->buffer, 16);

  // Validate the perso LTV object size.
  if (obj_size == 0) {
    LOG_ERROR(
        "Inconsistent certificate perso LTV object header %02x %02x at "
        "page %x",
        cert_buffer->buffer[0], cert_buffer->buffer[1],
        mldsa_endorsed_cert_pages[0]->base_addr);
    return DATA_LOSS();
  }

  TRY_CHECK(obj_size == expected_cert->obj_size);

  if (obj_size > (ARRAYSIZE(mldsa_endorsed_cert_pages) *
                  FLASH_CTRL_PARAM_BYTES_PER_PAGE)) {
    LOG_ERROR("Bad certificate perso LTV object size %d at page %x", obj_size,
              mldsa_endorsed_cert_pages[0]->base_addr);
    return DATA_LOSS();
  }

  // Read the entire perso LTV object from flash and compare it against expected
  // certificate. Then hash the data from expected certificate

  for (size_t i = 0; i < ARRAYSIZE(mldsa_endorsed_cert_pages); i++) {
    static_assert(
        (FLASH_CTRL_PARAM_BYTES_PER_PAGE % sizeof(cert_buffer->buffer)) == 0,
        "Following logic to read data from flash info page expects that flash "
        "info page size is a multiple of the scratch buffer size");
    for (size_t j = 0;
         j < (FLASH_CTRL_PARAM_BYTES_PER_PAGE / sizeof(cert_buffer->buffer));
         j++) {
      const size_t obj_offset = (i * FLASH_CTRL_PARAM_BYTES_PER_PAGE) +
                                (j * sizeof(cert_buffer->buffer));
      if (expected_cert->obj_size > obj_offset) {
        const size_t obj_size_left = min(expected_cert->obj_size - obj_offset,
                                         sizeof(cert_buffer->buffer));
        TRY(flash_ctrl_info_read(
            mldsa_endorsed_cert_pages[i],
            /*page_offset=*/j * sizeof(cert_buffer->buffer),
            util_size_to_words(obj_size_left), cert_buffer->buffer));
        TRY_CHECK(memcmp(expected_cert->obj_p + obj_offset, cert_buffer->buffer,
                         obj_size_left) == 0);
      }
    }
  }
  hmac_sha256_update(expected_cert->cert_body_p, expected_cert->cert_body_size);

  return OK_STATUS();
}

status_t personalize_extension_post_cert_endorse(
    personalize_extension_post_endorse_t *post_params) {
  // Find MLDSA UDS cert in perso blob and extract it
  perso_blob_t *blob_from_host = post_params->perso_blob_from_host;
  perso_tlv_cert_obj_view_t cert;
  TRY(extract_mldsa_uds_cert(blob_from_host, &cert));

  // Check that the cert will fit inside allocated pages
  TRY_CHECK(cert.obj_size <= (ARRAYSIZE(mldsa_endorsed_cert_pages) *
                              FLASH_CTRL_PARAM_BYTES_PER_PAGE));

  static cert_scratch_buffer_t cert_buffer;
  TRY(write_certificate(&cert_buffer, &cert));

  return hash_certificate(&cert_buffer, &cert);
}
