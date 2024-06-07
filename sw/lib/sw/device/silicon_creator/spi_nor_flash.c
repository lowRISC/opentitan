// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/lib/sw/device/silicon_creator/spi_nor_flash.h"

#include <stddef.h>
#include <stdint.h>

#include "sw/device/silicon_creator/lib/drivers/spi_host.h"
#include "sw/lib/sw/device/silicon_creator/base/sec_mmio.h"

#include "hw/top_darjeeling/sw/autogen/top_darjeeling.h"

static rom_error_t spi_nor_flash_reset(uint32_t csid) {
  spi_host_segment_t segment = {
      .type = kSpiHostSegmentTypeOpcode,
  };

  // Send the Reset command sequence
  segment.opcode.opcode = 0x66;  // Enable Reset
  RETURN_IF_ERROR(spi_host_transaction(csid, &segment, 1));
  segment.opcode.opcode = 0x99;  // Reset
  RETURN_IF_ERROR(spi_host_transaction(csid, &segment, 1));

  return kErrorOk;
}

static rom_error_t spi_nor_flash_read_jedec_id(uint32_t csid,
                                               uint32_t *jedec_id) {
  spi_host_segment_t segments[2] = {
      {
          .type = kSpiHostSegmentTypeOpcode,
          .opcode =
              {
                  .opcode = 0x9f,  // Read JEDEC ID
              },
      },
      {
          .type = kSpiHostSegmentTypeRx,
          .rx =
              {
                  .buf = (uint8_t *)jedec_id,
                  .length = 3,
              },
      },
  };
  RETURN_IF_ERROR(spi_host_transaction(csid, segments, ARRAYSIZE(segments)));

  // Convert JEDEC ID to correct endianness and only keep 24-bit
  *jedec_id = __builtin_bswap32(*jedec_id) >> 8;

  return kErrorOk;
}

static rom_error_t spi_nor_flash_exit_4b_address_mode(uint32_t csid) {
  spi_host_segment_t segment = {
      .type = kSpiHostSegmentTypeOpcode,
      .opcode =
          {
              .opcode = 0xe9,  // Exit 4-Byte Address Mode
          },
  };
  RETURN_IF_ERROR(spi_host_transaction(csid, &segment, 1));

  return kErrorOk;
}

OT_WARN_UNUSED_RESULT
rom_error_t spi_nor_flash_init(uint32_t csid, uint32_t *jedec_id) {
  // Send reset sequence to memory
  RETURN_IF_ERROR(spi_nor_flash_reset(csid));

  // Exit 4 byte address mode (harmless if not supported by the flash)
  RETURN_IF_ERROR(spi_nor_flash_exit_4b_address_mode(csid));

  // Read JEDEC ID
  uint32_t jid = 0;
  RETURN_IF_ERROR(spi_nor_flash_read_jedec_id(csid, &jid));

  // Check for invalid JEDEC ID values
  if (jid == 0 || jid == 0xffffff) {
    return kErrorSpiNorFlashNotFound;
  }

  if (jedec_id) {
    *jedec_id = jid;
  }

  return kErrorOk;
}

OT_WARN_UNUSED_RESULT
rom_error_t spi_nor_flash_read(uint32_t csid, uint32_t addr,
                               uint32_t byte_count, void *data) {
  // Make sure address fits in 3 bytes
  if (addr >= (1 << 24)) {
    return kErrorSpiNorFlashInvalidArgument;
  }

  spi_host_segment_t segments[4] = {
      {
          .type = kSpiHostSegmentTypeOpcode,
          .opcode =
              {
                  .opcode = 0x0b,  // Fast Read
              },
      },
      {
          .type = kSpiHostSegmentTypeAddress,
          .address =
              {
                  .mode = kSpiHostAddrMode3b,
                  .address = addr,
              },
      },
      {
          .type = kSpiHostSegmentTypeDummy,
          .dummy =
              {
                  .length = 8,
              },
      },
      {
          .type = kSpiHostSegmentTypeRx,
          .rx =
              {
                  .buf = data,
                  .length = byte_count,
              },
      },
  };
  RETURN_IF_ERROR(spi_host_transaction(csid, segments, ARRAYSIZE(segments)));

  return kErrorOk;
}
