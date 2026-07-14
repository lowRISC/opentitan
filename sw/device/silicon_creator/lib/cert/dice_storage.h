// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_CERT_DICE_STORAGE_H_
#define OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_CERT_DICE_STORAGE_H_

#include "sw/device/lib/base/macros.h"
#include "sw/device/silicon_creator/lib/drivers/flash_ctrl.h"
#include "sw/device/silicon_creator/lib/drivers/hmac.h"
#include "sw/device/silicon_creator/lib/error.h"
#include "sw/device/silicon_creator/manuf/base/perso_tlv_data.h"

#include "flash_ctrl_regs.h"  // Generated.

#ifdef __cplusplus
extern "C" {
#endif

enum {
  kDiceStoragePageDataSize = FLASH_CTRL_PARAM_BYTES_PER_PAGE -
                             (2 * sizeof(uint64_t) + sizeof(hmac_digest_t)),
};

typedef struct dice_storage_header {
  uint16_t object_header;  // Big Endian
  uint16_t cert_header;    // Big Endian
  char name[12];           // "CDI_0" or "CDI_1", padded with 0
} dice_storage_header_t;

OT_ASSERT_MEMBER_OFFSET(dice_storage_header_t, object_header, 0);
OT_ASSERT_MEMBER_OFFSET(dice_storage_header_t, cert_header, 2);
OT_ASSERT_MEMBER_OFFSET(dice_storage_header_t, name, 4);
OT_ASSERT_SIZE(dice_storage_header_t, 16);

typedef struct dice_storage_slot {
  const flash_ctrl_info_page_t *info_page;
  uint32_t page_offset;
  dice_storage_header_t header;  // Template
  uint8_t header_size;
  uint16_t data_size;
} dice_storage_slot_t;

#define DICE_STORAGE_SLOT(name_str, info_page_ptr, offset_val, slot_size_val, \
                          type_val)                                           \
  {                                                                           \
    .info_page = info_page_ptr, .page_offset = offset_val,                    \
    .header =                                                                 \
        {                                                                     \
            .object_header = TLV_OBJ_HEADER(type_val, slot_size_val),         \
            .cert_header = TLV_CERT_HEADER(sizeof(name_str) - 1, 0),          \
            .name = name_str,                                                 \
        },                                                                    \
    .header_size = 4 + sizeof(name_str) - 1,                                  \
    .data_size = slot_size_val - (4 + sizeof(name_str) - 1),                  \
  }

/**
 * DICE key ID indexes.
 *
 * Note that the CDI_0 index is at index 1, which is physically closer to the
 * digest at the bottom.
 */
typedef enum dice_key_id_index {
  kDicePageKeyIdxCdi1 = 0,
  kDicePageKeyIdxCdi0 = 1,
} dice_key_id_index_t;

/**
 * The flash page schema for holding DICE certificates.
 */
typedef struct dice_storage_page {
  uint8_t data[kDiceStoragePageDataSize];
  uint64_t cdi_key_ids[2];
  hmac_digest_t digest;
} dice_storage_page_t;

OT_ASSERT_MEMBER_OFFSET(dice_storage_page_t, data, 0);
OT_ASSERT_MEMBER_OFFSET(dice_storage_page_t, cdi_key_ids, 2000);
OT_ASSERT_MEMBER_OFFSET(dice_storage_page_t, digest, 2016);
OT_ASSERT_SIZE(dice_storage_page_t, FLASH_CTRL_PARAM_BYTES_PER_PAGE);

/**
 * The DICE page (2048 bytes) is divided into two certificate slots and a
 * metadata block at the end.
 *
 * The slot size is configurable in each DICE variant; the following example
 * illustrates the layout with 936-byte slots.
 *
 * Note: Although the offset is hardcoded in the rom_ext implementation,
 * OwnerSw clients should still parse the TLV structure dynamically to ensure
 * future layout changes do not break compatibility.
 *
 * +--------------------------------------------------------------------------+
 * |                         DiceCerts Page (2048 B)                          |
 * +--------------------------------------------------------------------------+
 * | TLV Object: CDI_0 (936 B)                                                |
 * | +----------------------------------------------------------------------+ |
 * | | Object Header (2 B): type=kPersoObjectTypeX509Cert, size=936B        | |
 * | +----------------------------------------------------------------------+ |
 * | | TLV Cert Object (9 B + len(cert) B)                                  | |
 * | | +------------------------------------------------------------------+ | |
 * | | | Cert Header (2 B): len(name)=5B, len(cert)=var-size              | | |
 * | | +------------------------------------------------------------------+ | |
 * | | | Cert Name (5 B): "CDI_0"                                         | | |
 * | | +------------------------------------------------------------------+ | |
 * | | | Cert Body: Cert Data (variable size)                             | | |
 * | | +------------------------------------------------------------------+ | |
 * | +----------------------------------------------------------------------+ |
 * | | Padding: Padded to 936 B                                             | |
 * | +----------------------------------------------------------------------+ |
 * +--------------------------------------------------------------------------+
 * | TLV Object: CDI_1 (936 B)                                                |
 * | +----------------------------------------------------------------------+ |
 * | | Object Header (2 B): type=kPersoObjectTypeX509Cert, size=936B        | |
 * | +----------------------------------------------------------------------+ |
 * | | TLV Cert Object (9 B + len(cert) B)                                  | |
 * | | +------------------------------------------------------------------+ | |
 * | | | Cert Header (2 B): len(name)=5B, len(cert)=var-size              | | |
 * | | +------------------------------------------------------------------+ | |
 * | | | Cert Name (5 B): "CDI_1"                                         | | |
 * | | +------------------------------------------------------------------+ | |
 * | | | Cert Body: Cert Data (variable size)                             | | |
 * | | +------------------------------------------------------------------+ | |
 * | +----------------------------------------------------------------------+ |
 * | | Padding: Padded to 936 B                                             | |
 * | +----------------------------------------------------------------------+ |
 * +--------------------------------------------------------------------------+
 * | Gap / Reserved (128 B)                                                   |
 * +--------------------------------------------------------------------------+
 * | Metadata Block: dice_page_meta_t (48 B)                                  |
 * | +----------------------------------------------------------------------+ |
 * | | cdi_1_key_id (8 B): Cache ID to skip regeneration                    | |
 * | +----------------------------------------------------------------------+ |
 * | | cdi_0_key_id (8 B): Cache ID to skip regeneration                    | |
 * | +----------------------------------------------------------------------+ |
 * | | digest (32 B): Integrity check for corruption or interrupted write   | |
 * | +----------------------------------------------------------------------+ |
 * +--------------------------------------------------------------------------+
 */
extern const dice_storage_slot_t kDiceStorageCdi0Ecdsa;
extern const dice_storage_slot_t kDiceStorageCdi1Ecdsa;

/**
 * Return pointer to the certificate header in a page slot.
 *
 * @param layout Slot layout.
 * @param page Pointer to the page in memory.
 * @return Pointer to the certificate header.
 */
inline dice_storage_header_t *dice_storage_slot_header(
    const dice_storage_slot_t *layout, dice_storage_page_t *page) {
  return (dice_storage_header_t *)((uint8_t *)page + layout->page_offset);
}

/**
 * Return pointer to the certificate data area in a page slot.
 *
 * @param layout Slot layout.
 * @param page Pointer to the page in memory.
 * @return Pointer to the certificate data.
 */
inline uint8_t *dice_storage_slot_data(const dice_storage_slot_t *layout,
                                       dice_storage_page_t *page) {
  return (uint8_t *)page + layout->page_offset + layout->header_size;
}

/**
 * Load the DICE certificates page from flash.
 *
 * @param page Destination buffer.
 * @return Error code.
 */
OT_WARN_UNUSED_RESULT
rom_error_t dice_storage_load_page(dice_storage_page_t *page);

/**
 * Write the DICE certificates page to flash after erasing it.
 *
 * @param page Source page data.
 * @return Error code.
 */
OT_WARN_UNUSED_RESULT
rom_error_t dice_storage_flush_page(const dice_storage_page_t *page);

/**
 * Read a DICE key ID from flash.
 *
 * @param index Key ID index (CDI_0 or CDI_1).
 * @param key_id Destination buffer.
 * @return Error code.
 */
OT_WARN_UNUSED_RESULT
rom_error_t dice_storage_get_key_id(dice_key_id_index_t index,
                                    uint64_t *key_id);

/**
 * Initialize a slot in the page buffer with its default header.
 *
 * @param layout Slot layout.
 * @param page Pointer to the page in memory.
 */
void dice_storage_slot_init(const dice_storage_slot_t *layout,
                            dice_storage_page_t *page);

/**
 * Set the actual certificate size in the slot header.
 *
 * @param layout Slot layout.
 * @param cert_size Actual size of the certificate.
 * @param page Pointer to the page in memory.
 */
void dice_storage_set_cert_size(const dice_storage_slot_t *layout,
                                size_t cert_size, dice_storage_page_t *page);

/**
 * Calculate the SHA256 digest of the certificates page.
 *
 * @param page Page data.
 * @param digest_out Destination buffer for the digest.
 */
void dice_storage_digest_page(const dice_storage_page_t *page,
                              hmac_digest_t *digest_out);

/**
 * Check if the digest in the page matches the page contents.
 *
 * @param page Page data.
 * @return Error code.
 */
OT_WARN_UNUSED_RESULT
rom_error_t dice_storage_check_digest(const dice_storage_page_t *page);

#ifdef __cplusplus
}
#endif

#endif  // OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_CERT_DICE_STORAGE_H_
