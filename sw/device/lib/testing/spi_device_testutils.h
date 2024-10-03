// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_TESTING_SPI_DEVICE_TESTUTILS_H_
#define OPENTITAN_SW_DEVICE_LIB_TESTING_SPI_DEVICE_TESTUTILS_H_

#include <assert.h>
#include <stdint.h>

#include "sw/device/lib/base/status.h"
#include "sw/device/lib/dif/dif_pinmux.h"
#include "sw/device/lib/dif/dif_spi_device.h"
#include "sw/device/lib/testing/json/spi_passthru.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

/**
 * A set of typical opcodes for named flash commands.
 */
typedef enum spi_device_flash_opcode {
  kSpiDeviceFlashOpReadJedec = 0x9f,
  kSpiDeviceFlashOpReadSfdp = 0x5a,
  kSpiDeviceFlashOpReadNormal = 0x03,
  kSpiDeviceFlashOpRead4b = 0x13,
  kSpiDeviceFlashOpReadFast = 0x0b,
  kSpiDeviceFlashOpReadFast4b = 0x0c,
  kSpiDeviceFlashOpReadDual = 0x3b,
  kSpiDeviceFlashOpReadQuad = 0x6b,
  kSpiDeviceFlashOpWriteEnable = 0x06,
  kSpiDeviceFlashOpWriteDisable = 0x04,
  kSpiDeviceFlashOpReadStatus1 = 0x05,
  kSpiDeviceFlashOpReadStatus2 = 0x35,
  kSpiDeviceFlashOpReadStatus3 = 0x15,
  kSpiDeviceFlashOpWriteStatus1 = 0x01,
  kSpiDeviceFlashOpWriteStatus2 = 0x31,
  kSpiDeviceFlashOpWriteStatus3 = 0x11,
  kSpiDeviceFlashOpChipErase = 0xc7,
  kSpiDeviceFlashOpSectorErase = 0x20,
  kSpiDeviceFlashOpBlockErase32k = 0x52,
  kSpiDeviceFlashOpBlockErase64k = 0xd8,
  kSpiDeviceFlashOpPageProgram = 0x02,
  kSpiDeviceFlashOpEnter4bAddr = 0xb7,
  kSpiDeviceFlashOpExit4bAddr = 0xe9,
  kSpiDeviceFlashOpResetEnable = 0x66,
  kSpiDeviceFlashOpReset = 0x99,
  kSpiDeviceFlashOpSectorErase4b = 0x21,
  kSpiDeviceFlashOpBlockErase32k4b = 0x5c,
  kSpiDeviceFlashOpBlockErase64k4b = 0xdc,
  kSpiDeviceFlashOpPageProgram4b = 0x12,
} spi_device_flash_opcode_t;

/**
 * The index where read and write commands begin in the command slots.
 */
enum spi_device_command_slot {
  kSpiDeviceReadCommandSlotBase = 0,
  kSpiDeviceWriteCommandSlotBase = 11,
};

/*
 * The SPI device pads for which `spi_device_testutils_configure_pad_attrs()`
 * configures the pad attributes.
 */
static const top_earlgrey_direct_pads_t spi_device_direct_pads[4] = {
    kTopEarlgreyDirectPadsSpiDeviceSd3,  // sio[3]
    kTopEarlgreyDirectPadsSpiDeviceSd2,  // sio[2]
    kTopEarlgreyDirectPadsSpiDeviceSd1,  // sio[1]
    kTopEarlgreyDirectPadsSpiDeviceSd0   // sio[0]
};

static const dif_spi_device_flash_command_t kReadCommands[] = {
    {
        // Slot 0: ReadStatus1
        .opcode = kSpiDeviceFlashOpReadStatus1,
        .address_type = kDifSpiDeviceFlashAddrDisabled,
        .dummy_cycles = 0,
        .payload_io_type = kDifSpiDevicePayloadIoSingle,
        .payload_dir_to_host = true,
    },
    {
        // Slot 1: ReadStatus2
        .opcode = kSpiDeviceFlashOpReadStatus2,
        .address_type = kDifSpiDeviceFlashAddrDisabled,
        .dummy_cycles = 0,
        .payload_io_type = kDifSpiDevicePayloadIoSingle,
        .payload_dir_to_host = true,
    },
    {
        // Slot 2: ReadStatus3
        .opcode = kSpiDeviceFlashOpReadStatus3,
        .address_type = kDifSpiDeviceFlashAddrDisabled,
        .dummy_cycles = 0,
        .payload_io_type = kDifSpiDevicePayloadIoSingle,
        .payload_dir_to_host = true,
    },
    {
        // Slot 3: ReadJedecID
        .opcode = kSpiDeviceFlashOpReadJedec,
        .address_type = kDifSpiDeviceFlashAddrDisabled,
        .dummy_cycles = 0,
        .payload_io_type = kDifSpiDevicePayloadIoSingle,
        .payload_dir_to_host = true,
    },
    {
        // Slot 4: ReadSfdp
        .opcode = kSpiDeviceFlashOpReadSfdp,
        .address_type = kDifSpiDeviceFlashAddr3Byte,
        .dummy_cycles = 8,
        .payload_io_type = kDifSpiDevicePayloadIoSingle,
        .payload_dir_to_host = true,
    },
    {
        // Slot 5: ReadNormal
        .opcode = kSpiDeviceFlashOpReadNormal,
        .address_type = kDifSpiDeviceFlashAddrCfg,
        .passthrough_swap_address = true,
        .dummy_cycles = 0,
        .payload_io_type = kDifSpiDevicePayloadIoSingle,
        .payload_dir_to_host = true,
    },
    {
        // Slot 6: ReadFast
        .opcode = kSpiDeviceFlashOpReadFast,
        .address_type = kDifSpiDeviceFlashAddrCfg,
        .passthrough_swap_address = true,
        .dummy_cycles = 8,
        .payload_io_type = kDifSpiDevicePayloadIoSingle,
        .payload_dir_to_host = true,
    },
    {
        // Slot 7: ReadDual
        .opcode = kSpiDeviceFlashOpReadDual,
        .address_type = kDifSpiDeviceFlashAddrCfg,
        .passthrough_swap_address = true,
        .dummy_cycles = 8,
        .payload_io_type = kDifSpiDevicePayloadIoDual,
        .payload_dir_to_host = true,
    },
    {
        // Slot 8: ReadQuad
        .opcode = kSpiDeviceFlashOpReadQuad,
        .address_type = kDifSpiDeviceFlashAddrCfg,
        .passthrough_swap_address = true,
        .dummy_cycles = 8,
        .payload_io_type = kDifSpiDevicePayloadIoQuad,
        .payload_dir_to_host = true,
    },
    {
        // Slot 9: Read4b
        .opcode = kSpiDeviceFlashOpRead4b,
        .address_type = kDifSpiDeviceFlashAddr4Byte,
        .passthrough_swap_address = true,
        .dummy_cycles = 0,
        .payload_io_type = kDifSpiDevicePayloadIoSingle,
        .payload_dir_to_host = true,
    },
    {
        // Slot 10: ReadFast4b
        .opcode = kSpiDeviceFlashOpReadFast4b,
        .address_type = kDifSpiDeviceFlashAddr4Byte,
        .passthrough_swap_address = true,
        .dummy_cycles = 8,
        .payload_io_type = kDifSpiDevicePayloadIoSingle,
        .payload_dir_to_host = true,
    },
};
static_assert(ARRAYSIZE(kReadCommands) <= UINT8_MAX,
              "Length of read_commands must fit in uint8_t or we must change "
              "the type of i.");

static const dif_spi_device_flash_command_t kWriteCommands[] = {
    {
        // Slot 11: WriteStatus1
        .opcode = kSpiDeviceFlashOpWriteStatus1,
        .address_type = kDifSpiDeviceFlashAddrDisabled,
        .payload_io_type = kDifSpiDevicePayloadIoSingle,
        .payload_dir_to_host = false,
        .upload = true,
        .set_busy_status = true,
    },
    {
        // Slot 12: WriteStatus2
        .opcode = kSpiDeviceFlashOpWriteStatus2,
        .address_type = kDifSpiDeviceFlashAddrDisabled,
        .payload_io_type = kDifSpiDevicePayloadIoSingle,
        .payload_dir_to_host = false,
        .upload = true,
        .set_busy_status = true,
    },
    {
        // Slot 13: WriteStatus3
        .opcode = kSpiDeviceFlashOpWriteStatus3,
        .address_type = kDifSpiDeviceFlashAddrDisabled,
        .payload_io_type = kDifSpiDevicePayloadIoSingle,
        .payload_dir_to_host = false,
        .upload = true,
        .set_busy_status = true,
    },
    {
        // Slot 14: ChipErase
        .opcode = kSpiDeviceFlashOpChipErase,
        .address_type = kDifSpiDeviceFlashAddrDisabled,
        .payload_io_type = kDifSpiDevicePayloadIoNone,
        .upload = true,
        .set_busy_status = true,
    },
    {
        // Slot 15: SectorErase
        .opcode = kSpiDeviceFlashOpSectorErase,
        .address_type = kDifSpiDeviceFlashAddrCfg,
        .payload_io_type = kDifSpiDevicePayloadIoNone,
        .upload = true,
        .set_busy_status = true,
    },
    {
        // Slot 16: BlockErase32k
        .opcode = kSpiDeviceFlashOpBlockErase32k,
        .address_type = kDifSpiDeviceFlashAddrCfg,
        .payload_io_type = kDifSpiDevicePayloadIoNone,
        .upload = true,
        .set_busy_status = true,
    },
    {
        // Slot 17: BlockErase64k
        .opcode = kSpiDeviceFlashOpBlockErase64k,
        .address_type = kDifSpiDeviceFlashAddrCfg,
        .payload_io_type = kDifSpiDevicePayloadIoNone,
        .upload = true,
        .set_busy_status = true,
    },
    {
        // Slot 18: PageProgram
        .opcode = kSpiDeviceFlashOpPageProgram,
        .address_type = kDifSpiDeviceFlashAddrCfg,
        .payload_io_type = kDifSpiDevicePayloadIoSingle,
        .payload_dir_to_host = false,
        .upload = true,
        .set_busy_status = true,
    },
    {
        // Slot 19: SectorErase4b
        .opcode = kSpiDeviceFlashOpSectorErase4b,
        .address_type = kDifSpiDeviceFlashAddr4Byte,
        .payload_io_type = kDifSpiDevicePayloadIoNone,
        .upload = true,
        .set_busy_status = true,
    },
    {
        // Slot 20: BlockErase32k4b
        .opcode = kSpiDeviceFlashOpBlockErase32k4b,
        .address_type = kDifSpiDeviceFlashAddr4Byte,
        .payload_io_type = kDifSpiDevicePayloadIoNone,
        .upload = true,
        .set_busy_status = true,
    },
    {
        // Slot 21: BlockErase64k4b
        .opcode = kSpiDeviceFlashOpBlockErase64k4b,
        .address_type = kDifSpiDeviceFlashAddr4Byte,
        .payload_io_type = kDifSpiDevicePayloadIoNone,
        .upload = true,
        .set_busy_status = true,
    },
    {
        // Slot 22: PageProgram4b
        .opcode = kSpiDeviceFlashOpPageProgram4b,
        .address_type = kDifSpiDeviceFlashAddr4Byte,
        .payload_io_type = kDifSpiDevicePayloadIoSingle,
        .payload_dir_to_host = false,
        .upload = true,
        .set_busy_status = true,
    },
    {
        // Slot 23: Reset
        .opcode = kSpiDeviceFlashOpReset,
        .address_type = kDifSpiDeviceFlashAddrDisabled,
        .payload_io_type = kDifSpiDevicePayloadIoNone,
        .upload = true,
        .set_busy_status = true,
    },

};
static_assert(ARRAYSIZE(kWriteCommands) <= UINT8_MAX,
              "Length of write_commands must fit into uint8_t");

/**
 * Configure the SPI device in passthrough mode, allowing the commands in the
 * provideded tables to pass through:
 *
 * @param spi_device A spi_device DIF handle.
 * @param filters A bitmap of command slots to enable passthrough filters for.
 * @param upload Whether to upload write commands.
 * @param write_cmds A table with the write commands to be configured.
 * @param write_cmds_size Num of elements in the write cmds table.
 * @param read_cmds A table with the read commands to be configured.
 * @param read_cmds_size Num of elements in the read cmds table.
 */
OT_WARN_UNUSED_RESULT
status_t spi_device_testutils_configure_passthrough(
    dif_spi_device_handle_t *spi_device, uint32_t filters, bool upload,
    const dif_spi_device_flash_command_t *write_cmds, size_t write_cmds_size,
    const dif_spi_device_flash_command_t *read_cmds, size_t read_cmds_size);

/**
 * Configure the read pipeline setting of the read command slots.
 *
 * Note that these settings can be overwritten by any other function that writes
 * the command slots. As such, this configuration should come after any function
 * calls that would affect dual read and quad read commands.
 *
 * @param spi_device A spi_device DIF handle.
 * @param dual_mode Desired read pipeline mode for the dual read command.
 * @param quad_mode Desired read pipeline mode for the quad read command.
 */
status_t spi_device_testutils_configure_read_pipeline(
    dif_spi_device_handle_t *spi_device,
    dif_spi_device_read_pipeline_mode_t dual_mode,
    dif_spi_device_read_pipeline_mode_t quad_mode);

/**
 * Configure the SPI device pad attributes.
 *
 * @return A status_t indicating success or failure configuring the pad
 * attributes.
 */
OT_WARN_UNUSED_RESULT
status_t spi_device_testutils_configure_pad_attrs(dif_pinmux_t *pinmux);

/**
 * Wait for a spi command upload.
 *
 * Upon detecting a spi command upload, the `info` block will be populated
 * with the opcode, address and data phases of the uploaded command.
 *
 * @param spid A spid_device DIF handle.
 * @param info Pointer to an upload_info_t.
 * @return A status_t indicating success or failure in receving the uploaded
 *         command.
 */
OT_WARN_UNUSED_RESULT
status_t spi_device_testutils_wait_for_upload(dif_spi_device_handle_t *spid,
                                              upload_info_t *info);

#endif  // OPENTITAN_SW_DEVICE_LIB_TESTING_SPI_DEVICE_TESTUTILS_H_
