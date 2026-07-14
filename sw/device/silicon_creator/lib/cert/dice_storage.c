// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/silicon_creator/lib/cert/dice_storage.h"

#include <stddef.h>
#include <string.h>

#include "sw/device/lib/base/macros.h"
#include "sw/device/lib/base/memory.h"
#include "sw/device/silicon_creator/lib/drivers/flash_ctrl.h"
#include "sw/device/silicon_creator/lib/drivers/hmac.h"
#include "sw/device/silicon_creator/lib/error.h"
#include "sw/device/silicon_creator/manuf/base/perso_tlv_data.h"

#include "flash_ctrl_regs.h"  // Generated.

extern dice_storage_header_t *dice_storage_slot_header(
    const dice_storage_slot_t *layout, dice_storage_page_t *page);

extern uint8_t *dice_storage_slot_data(const dice_storage_slot_t *layout,
                                       dice_storage_page_t *page);

rom_error_t dice_storage_load_page(dice_storage_page_t *page) {
  return flash_ctrl_info_read_zeros_on_read_error(
      &kFlashCtrlInfoPageDiceCerts, 0,
      sizeof(dice_storage_page_t) / sizeof(uint32_t), page);
}

rom_error_t dice_storage_flush_page(const dice_storage_page_t *page) {
  RETURN_IF_ERROR(flash_ctrl_info_erase(&kFlashCtrlInfoPageDiceCerts,
                                        kFlashCtrlEraseTypePage));
  return flash_ctrl_info_write(&kFlashCtrlInfoPageDiceCerts, 0,
                               sizeof(dice_storage_page_t) / sizeof(uint32_t),
                               page);
}

rom_error_t dice_storage_get_key_id(dice_key_id_index_t index,
                                    uint64_t *key_id) {
  return flash_ctrl_info_read_zeros_on_read_error(
      &kFlashCtrlInfoPageDiceCerts,
      offsetof(dice_storage_page_t, cdi_key_ids) + index * sizeof(uint64_t),
      sizeof(uint64_t) / sizeof(uint32_t), key_id);
}

void dice_storage_slot_init(const dice_storage_slot_t *layout,
                            dice_storage_page_t *page) {
  uint8_t *header_ptr = (uint8_t *)dice_storage_slot_header(layout, page);
  memset(header_ptr, 0, layout->header_size + layout->data_size);
  memcpy(header_ptr, &layout->header, sizeof(layout->header));
}

void dice_storage_set_cert_size(const dice_storage_slot_t *layout,
                                size_t cert_size, dice_storage_page_t *page) {
  dice_storage_header_t *header = dice_storage_slot_header(layout, page);
  size_t wrapped_size =
      layout->header_size - sizeof(layout->header.object_header) + cert_size;
  PERSO_TLV_SET_FIELD(Crth, Size, header->cert_header, wrapped_size);
}

void dice_storage_digest_page(const dice_storage_page_t *page,
                              hmac_digest_t *digest_out) {
  hmac_sha256(page, sizeof(dice_storage_page_t) - sizeof(hmac_digest_t),
              digest_out);
}

rom_error_t dice_storage_check_digest(const dice_storage_page_t *page) {
  hmac_digest_t actual;
  dice_storage_digest_page(page, &actual);

  if (memcmp(&actual, &page->digest, sizeof(hmac_digest_t)) != 0) {
    return kErrorDicePageCorrupted;
  }

  return kErrorOk;
}
