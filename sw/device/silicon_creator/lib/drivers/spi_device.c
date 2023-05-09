// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/silicon_creator/lib/drivers/spi_device.h"

#include "sw/device/lib/base/abs_mmio.h"
#include "sw/device/lib/base/bitfield.h"
#include "sw/device/lib/base/memory.h"
#include "sw/device/silicon_creator/lib/drivers/lifecycle.h"
#include "sw/device/silicon_creator/lib/error.h"

#include "flash_ctrl_regs.h"
#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"
#include "spi_device_regs.h"

enum {
  /**
   * Base address of the spi_device registers.
   */
  kBase = TOP_EARLGREY_SPI_DEVICE_BASE_ADDR,
  /**
   * Start address of the SFDP space in spi_device buffer.
   */
  kSfdpAreaStartAddr =
      kBase + SPI_DEVICE_BUFFER_REG_OFFSET + kSpiDeviceSfdpAreaOffset,
  /**
   * End address (exclusive) of the SFDP space in spi_device buffer.
   */
  kSfdpAreaEndAddr = kBase + SPI_DEVICE_BUFFER_REG_OFFSET +
                     kSpiDeviceSfdpAreaOffset + kSpiDeviceSfdpAreaNumBytes,
  /**
   * Flash data partition size in bits.
   */
  kFlashBitCount =
      FLASH_CTRL_PARAM_REG_NUM_BANKS * FLASH_CTRL_PARAM_BYTES_PER_BANK * 8,
  /**
   * 32-bit SFDP signature that indicates the presence of a SFDP table
   * (JESD216F 6.2.1).
   */
  kSfdpSignature = 0x50444653,
  /**
   * Number of parameter headers in the SFDP data structure (JESD216F 6.2.2).
   *
   * This number is zero-based. OpenTitan currently only has a single parameter
   * header for the Basic Flash Parameters Table (BFPT).
   */
  kSfdpParamCount = 0,
  /**
   * SFDP major revision number (JESD216F 6.2.2).
   */
  kSfdpMajorRevision = 0x01,
  /**
   * SFDP minor revision number (JESD216F 6.2.2).
   */
  kSfdpMinorRevision = 0x0a,
  /**
   * 3-byte addressing for SFDP_READ command, 8 wait states (JESD216F 6.2.3).
   */
  kSfdpAccessProtocol = 0xff,
  /**
   * BFPT major revision number (JESD216F 6.4.1).
   */
  kBfptMajorRevision = 0x01,
  /**
   * BFPT minor revision number (JESD216F 6.4.1).
   */
  kBfptMinorRevision = 0x07,
  /**
   * LSB of BFPT's parameter ID (JESD216F 6.4.1).
   */
  kBfptParamIdLsb = 0x00,
  /**
   * MSB of BFPT's parameter ID (JESD216F 6.4.2).
   */
  kBfptParamIdMsb = 0xff,
  /**
   * Offset of the Basic Flash Parameter Table (BFPT) in the SFDP table.
   */
  kBfptTablePointer = offsetof(spi_device_sfdp_table_t, bfpt),
  /**
   * Value used for BFPT fields that are not supported.
   *
   * Note: A handful of BFPT fields, e.g. Msb of the 14th word of BFPT, use 1
   * instead. Such fields should be defined according to JESD216F instead of
   * using this value.
   */
  kBfptNotSupported = 0,
};

static_assert(kBfptTablePointer % sizeof(uint32_t) == 0,
              "BFPT must be word-aligned");

/**
 * Computes the width of a field in a Basic Flash Parameters Table (BFPT) word.
 *
 * @param upper Upper (start) bit of the field (inclusive).
 * @param lower Lower (end) bit of the field (inclusive).
 */
#define BFPT_FIELD_WIDTH(upper, lower) ((upper) - (lower) + 1)

/**
 * Computes the mask for a field in a BFPT word.
 *
 * @param upper Upper (start) bit of the field (inclusive).
 * @param lower Lower (end) bit of the field (inclusive).
 */
#define BFPT_FIELD_MASK(upper, lower) \
  (((UINT64_C(1) << BFPT_FIELD_WIDTH(upper, lower)) - 1) << (lower))

/**
 * Computes the value of a field in a BFPT word.
 *
 * Bits outside the field are left as 1s. This macro is intended for expanding a
 * list of fields, e.g. `BFPT_WORD_1`, to compute the value of a BFPT word using
 * bitwise AND.
 *
 * @param upper Upper (start) bit of the field (inclusive).
 * @param lower Lower (end) bit of the field (inclusive).
 * @param value Value of the field.
 */
#define BFPT_FIELD_VALUE(upper, lower, value) \
  ((uint32_t)~BFPT_FIELD_MASK(upper, lower) | \
   (BFPT_FIELD_MASK(upper, lower) & ((uint32_t)(value) << (uint32_t)(lower))))

// Note: Words below are numbered starting from 1 to match JESD216F. Some fields
// that are not supported by OpenTitan are merged for the sake of conciseness.
// Unused/reserved fields that should be set to all 1s are ommitted due to the
// definition of `BFPT_FIELD_VALUE()` above. See JESD216F for more details.

// clang-format off
/**
 * BFPT 1st Word
 * -------------
 * [31:23]: Unused
 * [22:19]: (1S-1S-4S) (1S-4S-4S) (1S-2S-2S) DTR Clock (not supported: 0x0)
 * [18:17]: Address bytes (3-byte only addressing: 0x0)
 * [16:16]: (1S-1S-2S) (not supported: 0x0)
 * [15: 8]: 4 KiB erase instruction (0x20)
 * [ 7: 5]: Unused
 * [ 4: 4]: Write enable instruction (use 0x06 for WREN: 0x1)
 * [ 3: 3]: Volatile block protect bits (solely volatile: 0x1)
 * [ 2: 2]: Write granularity (buffer >= 64 B: 0x1)
 * [ 1: 0]: Block/sector erase sizes (uniform 4 KiB erase: 0x1)
 */
#define BFPT_WORD_1(X) \
  X(22, 19, kBfptNotSupported) & \
  X(18, 17, 0x0) & \
  X(16, 16, kBfptNotSupported) & \
  X(15,  8, kSpiDeviceOpcodeSectorErase) & \
  X( 4,  4, 0x1) & \
  X( 3,  3, 0x1) & \
  X( 2,  2, 0x1) & \
  X( 1,  0, 0x1)

/**
 * BFPT 2nd Word
 * -------------
 * [31:31]: Density greater than 2 Gib (0x0)
 * [30: 0]: Flash memory density in bits, zero-based (0x7fffff)
 */
#define BFPT_WORD_2(X) \
  X(31, 31, 0x0) & \
  X(30,  0, kFlashBitCount - 1)

/**
 * BFPT 3rd Word
 * -------------
 * [31: 0]: Fast read (1S-4S-4S) (1S-1S-4S) (not supported, 0x0)
 */
#define BFPT_WORD_3(X) \
  X(31,  0, kBfptNotSupported)

/**
 * BFPT 4th Word
 * -------------
 * [31: 0]: Fast read (1S-1S-2S) (1S-2S-2S) (not supported, 0x0)
 */
#define BFPT_WORD_4(X) \
  X(31,  0, kBfptNotSupported)

/**
 * BFPT 5th Word
 * -------------
 * [31: 5]: Reserved
 * [ 4: 4]: Fast read (4S-4S-4S) support (not supported, 0x0)
 * [ 3: 1]: Reserved
 * [ 0: 0]: Fast read (2S-2S-2S) support (not supported, 0x0)
 */
#define BFPT_WORD_5(X) \
  X( 4,  4, kBfptNotSupported) & \
  X( 0,  0, kBfptNotSupported)

/**
 * BFPT 6th Word
 * -------------
 * [31:16]: Fast read (2S-2S-2S) (not supported, 0x0)
 * [15: 0]: Reserved
 */
#define BFPT_WORD_6(X) \
  X(31, 16, kBfptNotSupported)

/**
 * BFPT 7th Word
 * -------------
 * [31:16]: Fast read (4S-4S-4S) (not supported, 0x0)
 * [15: 0]: Reserved
 */
#define BFPT_WORD_7(X) \
  X(31, 16, kBfptNotSupported)

/**
 * BFPT 8th Word
 * -------------
 * [31:16]: Erase type 2 instruction and size (not supported, 0x0)
 * [15: 8]: Erase type 1 instruction (0x20)
 * [ 7: 0]: Erase type 1 size (4 KiB, 2^N bytes, N = 0x0c)
 */
#define BFPT_WORD_8(X) \
  X(31, 16, kBfptNotSupported) & \
  X(15,  8, kSpiDeviceOpcodeSectorErase) & \
  X( 7,  0, 0x0c)

/**
 * BFPT 9th Word
 * -------------
 * [31: 0]: Erase type 4 and 3 (not supported, 0x0)
 */
#define BFPT_WORD_9(X) \
  X(31,  0, kBfptNotSupported)

/**
 * BFPT 10th Word
 * --------------
 * [31:11]: Erase 4,3,2 typical time (not supported, 0x0)
 * [10: 9]: Erase type 1 time unit (16 ms, 0x1)
 * [ 8: 4]: Erase type 1 time count, zero-based (0x8)
 *          formula: (count + 1) * unit
 *          (8 + 1) * 16 ms = 144 ms
 * [ 3: 0]: Max erase time multiplier, zero-based (0x6)
 *          formula: 2 * (multiplier + 1) * erase_time
 */
#define BFPT_WORD_10(X) \
  X(31, 11, kBfptNotSupported) & \
  X(10,  9, 0x1) & \
  X( 8,  4, 0x8) & \
  X( 3,  0, 0x0)

/**
 * BFPT 11th Word
 * --------------
 * [31:31]: Reserved
 * [30:29]: Chip erase time units (16 ms, 0x0)
 * [28:24]: Chip erase time count, zero-based (0xb)
 *          formula: (count + 1) * unit
 *          (11 + 1) * 16 ms = 192 ms
 * [23:23]: Additional byte program time units (8 us, 0x1)
 * [22:19]: Additional byte program time count, zero-based (0x5)
 *          formula: (count + 1) * unit
 *          (5 + 1) * 8 us = 48 us
 * [18:18]: First byte program time unit (8 us, 0x1)
 * [17:14]: First byte program time count, zero-based (0x5)
 *          formula: (count + 1) * unit
 *          (5 + 1) * 8 us = 48 us
 * [13:13]: Page program time unit (64 us, 0x1)
 * [12: 8]: Page program time count, zero-based (0xb)
 *          formula: (count + 1) * unit
 *          (11 + 1) * 64 us = 768 us
 * [ 7: 4]: Page size, 2^N (0x8)
 * [ 3: 0]: Max program time multiplier, zero-based (0x0)
 *          formula: 2 * (multiplier + 1) * program_time
 */
#define BFPT_WORD_11(X) \
 X(30, 29, 0x0) & \
 X(28, 24, 0xb) & \
 X(23, 23, 0x1) & \
 X(22, 19, 0x5) & \
 X(18, 18, 0x1) & \
 X(17, 14, 0x5) & \
 X(13, 13, 0x1) & \
 X(12,  8, 0xb) & \
 X( 7,  4, 0x8) & \
 X( 3,  0, 0x0)

/**
 * BFPT 12th Word
 * --------------
 * [31:31]: Suspend/Resume supported (not supported, 0x1)
 * [30: 9]: Suspend/Resume latencies for erase & program (not supported)
 * [ 8: 8]: Reserved
 * [ 7: 0]: Prohibited ops during suspend (not supported, 0x0)
 */
#define BFPT_WORD_12(X) \
 X(31, 31, 0x1) & \
 X(30,  9, kBfptNotSupported) & \
 X( 7,  0, kBfptNotSupported)

/**
 * BFPT 13th Word
 * --------------
 * [31: 0]: Erase/program suspend/resume instructions (not supported, 0x0)
 */
#define BFPT_WORD_13(X) \
 X(31, 0, kBfptNotSupported)

/**
 * BFPT 14th Word
 * --------------
 * [31:31]: Deep powerdown support (not supported, 0x1)
 * [30: 8]: Deep powerdown instructions and delay (not supported, 0x0)
 * [ 7: 2]: Busy polling (bit 0 using 0x05 instruction, 0x1)
 * [ 1: 0]: Reserved
 */
#define BFPT_WORD_14(X) \
 X(31, 31, 0x1) & \
 X(30,  8, kBfptNotSupported) & \
 X( 7,  2, 0x1)

/**
 * BFPT 15th Word
 * --------------
 * [31:24]: Reserved
 * [23: 0]: Hold, QE, (4S-4S-4S), 0-4-4 (not supported, 0x0)
 */
#define BFPT_WORD_15(X) \
 X(23,  0, kBfptNotSupported)

/**
 * BFPT 16th Word
 * --------------
 * [31:14]: 4-Byte addressing (not supported, 0x0)
 * [13: 8]: Soft-reset (0x66/0x99 sequence, 0x10)
 * [ 7: 7]: Reserved
 * [ 6: 0]: Status register (read-only, 0x0)
 */
#define BFPT_WORD_16(X) \
  X(31, 14, kBfptNotSupported) & \
  X(13,  8, 0x10) & \
  X( 6,  0, 0x0)

/**
 * BFPT 17th Word
 * --------------
 * [31:  0]: Fast read (1S-8S-8S) (1S-1S-8S) (not supported, 0x0)
 */
#define BFPT_WORD_17(X) \
  X(31,  0, kBfptNotSupported)

/**
 * BFPT 18th Word
 * --------------
 * [31,  0]: Data strobe, SPI protocol reset, etc. (not supported, 0x0)
 *
 * Note: Reserved fields of this word should be 0 (JESD216F 6.4.21).
 */
#define BFPT_WORD_18(X) \
  X(31,  0, kBfptNotSupported)

/**
 * BFPT 19th Word
 * --------------
 * [31,  0]: Octable enable, (8D-8D-8D), 0-8-8 mode (not suported, 0x0)
 *
 * Note: Reserved fields of this word should be 0 (JESD216F 6.4.22).
 */
#define BFPT_WORD_19(X) \
  X(31,  0, kBfptNotSupported)

/**
 * BFPT 20th Word
 * --------------
 * [31,  0]: Max (8S-8S-8S) (4D-4D-4D) (4S-4S-4S) speed
 *           (not supported, 0xffffffff)
 */
#define BFPT_WORD_20(X) \
  X(31,  0, UINT32_MAX)

/**
 * BFPT 21st Word
 * --------------
 * [31,  0]: Fast read support for various modes (not supported, 0x0)
 *
 * Note: Reserved fields of this word should be 0 (JESD216F 6.4.24).
 */
#define BFPT_WORD_21(X) \
  X(31,  0, kBfptNotSupported)

/**
 * BFPT 22nd Word
 * --------------
 * [31,  0]: Fast read (1S-1D-1D) (1S-2D-2D) (not supported, 0x0)
 */
#define BFPT_WORD_22(X) \
  X(31,  0, kBfptNotSupported)

/**
 * BFPT 23rd Word
 * --------------
 * [31,  0]: Fast read (1S-4D-4D) (4S-2D-2D) (not supported, 0x0)
 */
#define BFPT_WORD_23(X) \
  X(31,  0, kBfptNotSupported)
// clang-format on

const spi_device_sfdp_table_t kSpiDeviceSfdpTable = {
    .sfdp_header =
        {
            .signature = kSfdpSignature,
            .minor_revision = kSfdpMinorRevision,
            .major_revision = kSfdpMajorRevision,
            .param_count = kSfdpParamCount,
            .access_protocol = kSfdpAccessProtocol,
        },
    .bfpt_header =
        {
            .param_id_lsb = kBfptParamIdLsb,
            .minor_revision = kBfptMinorRevision,
            .major_revision = kBfptMajorRevision,
            .table_word_count = kSpiDeviceBfptNumWords,
            .table_pointer = {kBfptTablePointer},
            .param_id_msb = kBfptParamIdMsb,
        },
    .bfpt = {{
        BFPT_WORD_1(BFPT_FIELD_VALUE),  BFPT_WORD_2(BFPT_FIELD_VALUE),
        BFPT_WORD_3(BFPT_FIELD_VALUE),  BFPT_WORD_4(BFPT_FIELD_VALUE),
        BFPT_WORD_5(BFPT_FIELD_VALUE),  BFPT_WORD_6(BFPT_FIELD_VALUE),
        BFPT_WORD_7(BFPT_FIELD_VALUE),  BFPT_WORD_8(BFPT_FIELD_VALUE),
        BFPT_WORD_9(BFPT_FIELD_VALUE),  BFPT_WORD_10(BFPT_FIELD_VALUE),
        BFPT_WORD_11(BFPT_FIELD_VALUE), BFPT_WORD_12(BFPT_FIELD_VALUE),
        BFPT_WORD_13(BFPT_FIELD_VALUE), BFPT_WORD_14(BFPT_FIELD_VALUE),
        BFPT_WORD_15(BFPT_FIELD_VALUE), BFPT_WORD_16(BFPT_FIELD_VALUE),
        BFPT_WORD_17(BFPT_FIELD_VALUE), BFPT_WORD_18(BFPT_FIELD_VALUE),
        BFPT_WORD_19(BFPT_FIELD_VALUE), BFPT_WORD_20(BFPT_FIELD_VALUE),
        BFPT_WORD_21(BFPT_FIELD_VALUE), BFPT_WORD_22(BFPT_FIELD_VALUE),
        BFPT_WORD_23(BFPT_FIELD_VALUE),
    }}};

/**
 * Configuration options for a SPI Flash command.
 */
typedef struct cmd_info {
  /**
   * Offset of the CMD_INFO register to set.
   */
  uint32_t reg_offset;
  /**
   * Instruction code.
   */
  uint8_t op_code;
  /**
   * Address.
   *
   * 3 bytes if true, no address if false.
   */
  bool address;
  /**
   * Number of dummy cycles.
   */
  uint8_t dummy_cycles;
  /**
   * Whether the command is handled in software.
   *
   * If this field is true, BUSY and UPLOAD bits of the CMD_INFO register will
   * be set. spi_device treats the bytes following the address as the payload.
   * Maximum payload size is 256 bytes and spi_device will overwrite the payload
   * area if a larger payload is received.
   */
  bool handled_in_sw;
} cmd_info_t;

/**
 * Configures the spi_device to handle the given command.
 *
 * @param cmd_info Configuration options for a SPI Flash command.
 */
static void cmd_info_set(cmd_info_t cmd_info) {
  // CMD_INFO registers share the same layout, the code below uses the macros of
  // the CMD_INFO_0 register.
  uint32_t reg = bitfield_field32_write(0, SPI_DEVICE_CMD_INFO_0_OPCODE_0_FIELD,
                                        cmd_info.op_code);
  reg = bitfield_field32_write(
      reg, SPI_DEVICE_CMD_INFO_0_ADDR_MODE_0_FIELD,
      cmd_info.address ? SPI_DEVICE_CMD_INFO_0_ADDR_MODE_0_VALUE_ADDR3B
                       : SPI_DEVICE_CMD_INFO_0_ADDR_MODE_0_VALUE_ADDRDISABLED);
  if (cmd_info.dummy_cycles > 0) {
    // `DUMMY_SIZE` field is zero-based.
    reg = bitfield_field32_write(reg, SPI_DEVICE_CMD_INFO_0_DUMMY_SIZE_0_FIELD,
                                 cmd_info.dummy_cycles - 1);
    reg = bitfield_bit32_write(reg, SPI_DEVICE_CMD_INFO_0_DUMMY_EN_0_BIT, true);
  }
  reg = bitfield_bit32_write(reg, SPI_DEVICE_CMD_INFO_0_UPLOAD_0_BIT,
                             cmd_info.handled_in_sw);
  reg = bitfield_bit32_write(reg, SPI_DEVICE_CMD_INFO_0_BUSY_0_BIT,
                             cmd_info.handled_in_sw);
  reg = bitfield_bit32_write(reg, SPI_DEVICE_CMD_INFO_0_VALID_0_BIT, true);
  abs_mmio_write32(kBase + cmd_info.reg_offset, reg);
}

void spi_device_init(void) {
  // CPOL = 0, CPHA = 0, MSb-first TX and RX, 3-byte addressing.
  uint32_t reg = bitfield_bit32_write(0, SPI_DEVICE_CFG_CPOL_BIT, false);
  reg = bitfield_bit32_write(reg, SPI_DEVICE_CFG_CPHA_BIT, false);
  reg = bitfield_bit32_write(reg, SPI_DEVICE_CFG_TX_ORDER_BIT, false);
  reg = bitfield_bit32_write(reg, SPI_DEVICE_CFG_RX_ORDER_BIT, false);
  reg = bitfield_field32_write(reg, SPI_DEVICE_CFG_TIMER_V_FIELD, 0x7f);
  reg = bitfield_bit32_write(reg, SPI_DEVICE_CFG_ADDR_4B_EN_BIT, false);
  reg = bitfield_bit32_write(reg, SPI_DEVICE_CFG_MAILBOX_EN_BIT, false);
  abs_mmio_write32(kBase + SPI_DEVICE_CFG_REG_OFFSET, reg);

  // JEDEC manufacturer and device ID.
  // spi_device sends these in the following order: continuation codes,
  // manufacturer ID, LSB of device ID, and MSB of device ID (density).
  reg = bitfield_field32_write(0, SPI_DEVICE_JEDEC_CC_CC_FIELD,
                               kSpiDeviceJedecContCode);
  reg = bitfield_field32_write(reg, SPI_DEVICE_JEDEC_CC_NUM_CC_FIELD,
                               kSpiDeviceJedecContCodeCount);
  abs_mmio_write32(kBase + SPI_DEVICE_JEDEC_CC_REG_OFFSET, reg);
  // Note: The code below assumes that chip revision and generation numbers
  // from the life cycle controller (16-bits each) will fit in the revision and
  // generation fields of the device ID (3 and 4 bits, respectively).
  lifecycle_hw_rev_t hw_rev;
  lifecycle_hw_rev_get(&hw_rev);
  // TODO: hw_rev mapping may have to be updated.
  reg = bitfield_field32_write(0, SPI_DEVICE_DEV_ID_CHIP_REV_FIELD,
                               hw_rev.revision_id);
  reg = bitfield_bit32_write(reg, SPI_DEVICE_DEV_ID_ROM_BOOTSTRAP_BIT, true);
  reg = bitfield_field32_write(reg, SPI_DEVICE_DEV_ID_CHIP_GEN_FIELD,
                               hw_rev.product_id);
  reg = bitfield_field32_write(reg, SPI_DEVICE_DEV_ID_DENSITY_FIELD,
                               kSpiDeviceJedecDensity);
  reg = bitfield_field32_write(reg, SPI_DEVICE_JEDEC_ID_MF_FIELD,
                               kSpiDeviceJedecManufId);
  abs_mmio_write32(kBase + SPI_DEVICE_JEDEC_ID_REG_OFFSET, reg);

  // Write SFDP table to the reserved region in spi_device buffer.
  uint32_t dest = kSfdpAreaStartAddr;
  const char *table = (const char *)&kSpiDeviceSfdpTable;
  for (size_t i = 0; i < kSpiDeviceSfdpTableNumWords; ++i) {
    abs_mmio_write32(dest, read_32(table));
    dest += sizeof(uint32_t);
    table += sizeof(uint32_t);
  }
  // Fill the remaining space with `0xff`s.
  for (; dest < kSfdpAreaEndAddr; dest += sizeof(uint32_t)) {
    abs_mmio_write32(dest, UINT32_MAX);
  }

  // Reset the payload buffer to prevent access faults when reading beyond
  // current payload depth (see #11782).
  for (size_t i = 0; i < kSpiDevicePayloadAreaNumBytes; i += sizeof(uint32_t)) {
    abs_mmio_write32(
        kBase + SPI_DEVICE_BUFFER_REG_OFFSET + kSpiDevicePayloadAreaOffset + i,
        0);
  }

  // Reset status register
  abs_mmio_write32(kBase + SPI_DEVICE_FLASH_STATUS_REG_OFFSET, 0);

  // Configure the READ_STATUS command (CMD_INFO_0).
  cmd_info_set((cmd_info_t){
      .reg_offset = SPI_DEVICE_CMD_INFO_0_REG_OFFSET,
      .op_code = kSpiDeviceOpcodeReadStatus,
      .address = false,
      .dummy_cycles = 0,
      .handled_in_sw = false,
  });
  // Configure the READ_JEDEC_ID command (CMD_INFO_3).
  cmd_info_set((cmd_info_t){
      .reg_offset = SPI_DEVICE_CMD_INFO_3_REG_OFFSET,
      .op_code = kSpiDeviceOpcodeReadJedecId,
      .address = false,
      .dummy_cycles = 0,
      .handled_in_sw = false,
  });
  // Configure the READ_SFDP command (CMD_INFO_4).
  cmd_info_set((cmd_info_t){
      .reg_offset = SPI_DEVICE_CMD_INFO_4_REG_OFFSET,
      .op_code = kSpiDeviceOpcodeReadSfdp,
      .address = true,
      .dummy_cycles = 8,
      .handled_in_sw = false,
  });
  // Configure the CHIP_ERASE command (CMD_INFO_11).
  cmd_info_set((cmd_info_t){
      .reg_offset = SPI_DEVICE_CMD_INFO_11_REG_OFFSET,
      .op_code = kSpiDeviceOpcodeChipErase,
      .address = false,
      .dummy_cycles = 0,
      .handled_in_sw = true,
  });
  // Configure the SECTOR_ERASE command (CMD_INFO_12).
  cmd_info_set((cmd_info_t){
      .reg_offset = SPI_DEVICE_CMD_INFO_12_REG_OFFSET,
      .op_code = kSpiDeviceOpcodeSectorErase,
      .address = true,
      .dummy_cycles = 0,
      .handled_in_sw = true,
  });
  // Configure the PAGE_PROGRAM command (CMD_INFO_13).
  cmd_info_set((cmd_info_t){
      .reg_offset = SPI_DEVICE_CMD_INFO_13_REG_OFFSET,
      .op_code = kSpiDeviceOpcodePageProgram,
      .address = true,
      .dummy_cycles = 0,
      .handled_in_sw = true,
  });
  // Configure the RESET command (CMD_INFO_14).
  cmd_info_set((cmd_info_t){
      .reg_offset = SPI_DEVICE_CMD_INFO_14_REG_OFFSET,
      .op_code = kSpiDeviceOpcodeReset,
      .address = false,
      .dummy_cycles = 0,
      .handled_in_sw = true,
  });
  // Configure the WRITE_ENABLE and WRITE_DISABLE commands.
  reg = bitfield_field32_write(0, SPI_DEVICE_CMD_INFO_WREN_OPCODE_FIELD,
                               kSpiDeviceOpcodeWriteEnable);
  reg = bitfield_bit32_write(reg, SPI_DEVICE_CMD_INFO_WREN_VALID_BIT, true);
  abs_mmio_write32(kBase + SPI_DEVICE_CMD_INFO_WREN_REG_OFFSET, reg);
  reg = bitfield_field32_write(reg, SPI_DEVICE_CMD_INFO_WRDI_OPCODE_FIELD,
                               kSpiDeviceOpcodeWriteDisable);
  abs_mmio_write32(kBase + SPI_DEVICE_CMD_INFO_WRDI_REG_OFFSET, reg);
}

rom_error_t spi_device_cmd_get(spi_device_cmd_t *cmd) {
  uint32_t reg = 0;
  bool cmd_pending = false;
  while (!cmd_pending) {
    // Note: Using INTR_STATE.UPLOAD_CMDFIFO_NOT_EMPTY because
    // UPLOAD_STATUS.CMDFIFO_NOTEMPTY is set before the SPI transaction ends.
    reg = abs_mmio_read32(kBase + SPI_DEVICE_INTR_STATE_REG_OFFSET);
    cmd_pending = bitfield_bit32_read(
        reg, SPI_DEVICE_INTR_COMMON_UPLOAD_CMDFIFO_NOT_EMPTY_BIT);
  }
  abs_mmio_write32(kBase + SPI_DEVICE_INTR_STATE_REG_OFFSET, UINT32_MAX);
  if (bitfield_bit32_read(reg,
                          SPI_DEVICE_INTR_COMMON_UPLOAD_PAYLOAD_OVERFLOW_BIT)) {
    return kErrorSpiDevicePayloadOverflow;
  }

  cmd->opcode = abs_mmio_read32(kBase + SPI_DEVICE_UPLOAD_CMDFIFO_REG_OFFSET);
  cmd->address = kSpiDeviceNoAddress;
  reg = abs_mmio_read32(kBase + SPI_DEVICE_UPLOAD_STATUS_REG_OFFSET);
  if (bitfield_bit32_read(reg,
                          SPI_DEVICE_UPLOAD_STATUS_ADDRFIFO_NOTEMPTY_BIT)) {
    cmd->address =
        abs_mmio_read32(kBase + SPI_DEVICE_UPLOAD_ADDRFIFO_REG_OFFSET);
  }

  reg = abs_mmio_read32(kBase + SPI_DEVICE_UPLOAD_STATUS2_REG_OFFSET);
  cmd->payload_byte_count =
      bitfield_field32_read(reg, SPI_DEVICE_UPLOAD_STATUS2_PAYLOAD_DEPTH_FIELD);
  // `payload_byte_count` can be at most `kSpiDevicePayloadAreaNumBytes`.
  HARDENED_CHECK_LE(cmd->payload_byte_count, kSpiDevicePayloadAreaNumBytes);
  uint32_t src =
      kBase + SPI_DEVICE_BUFFER_REG_OFFSET + kSpiDevicePayloadAreaOffset;
  char *dest = (char *)&cmd->payload;
  for (size_t i = 0; i < cmd->payload_byte_count; i += sizeof(uint32_t)) {
    write_32(abs_mmio_read32(src + i), dest + i);
  }

  return kErrorOk;
}

void spi_device_flash_status_clear(void) {
  abs_mmio_write32(kBase + SPI_DEVICE_FLASH_STATUS_REG_OFFSET, 0);
}

uint32_t spi_device_flash_status_get(void) {
  return abs_mmio_read32(kBase + SPI_DEVICE_FLASH_STATUS_REG_OFFSET);
}
