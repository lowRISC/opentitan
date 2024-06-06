// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_HW_TOP_DARJEELING_SW_AUTOGEN_TOP_DARJEELING_SOC_MBX_MEMORY_H_
#define OPENTITAN_HW_TOP_DARJEELING_SW_AUTOGEN_TOP_DARJEELING_SOC_MBX_MEMORY_H_

#include "top_darjeeling_flash_ctrl_dummy.h"
#include "top_darjeeling_keymgr_dummy.h"

/**
 * @file
 * @brief Assembler-only Top-Specific Definitions.
 *
 * This file contains preprocessor definitions for use within assembly code.
 *
 * These are not shared with C/C++ code because these are only allowed to be
 * preprocessor definitions, no data or type declarations are allowed. The
 * assembler is also stricter about literals (not allowing suffixes for
 * signed/unsigned which are sensible to use for unsigned values in C/C++).
 */

// Include guard for assembler
#ifdef __ASSEMBLER__



/**
 * Peripheral base address for soc device on mbx0 in top darjeeling.
 *
 * This should be used with #mmio_region_from_addr to access the memory-mapped
 * registers associated with the peripheral (usually via a DIF).
 */
#define TOP_DARJEELING_MBX0_SOC_BASE_ADDR 0x1465000

/**
 * Peripheral size for soc device on mbx0 in top darjeeling.
 *
 * This is the size (in bytes) of the peripheral's reserved memory area. All
 * memory-mapped registers associated with this peripheral should have an
 * address between #TOP_DARJEELING_MBX0_SOC_BASE_ADDR and
 * `TOP_DARJEELING_MBX0_SOC_BASE_ADDR + TOP_DARJEELING_MBX0_SOC_SIZE_BYTES`.
 */
#define TOP_DARJEELING_MBX0_SOC_SIZE_BYTES 0x20
/**
 * Peripheral base address for soc device on mbx1 in top darjeeling.
 *
 * This should be used with #mmio_region_from_addr to access the memory-mapped
 * registers associated with the peripheral (usually via a DIF).
 */
#define TOP_DARJEELING_MBX1_SOC_BASE_ADDR 0x1465100

/**
 * Peripheral size for soc device on mbx1 in top darjeeling.
 *
 * This is the size (in bytes) of the peripheral's reserved memory area. All
 * memory-mapped registers associated with this peripheral should have an
 * address between #TOP_DARJEELING_MBX1_SOC_BASE_ADDR and
 * `TOP_DARJEELING_MBX1_SOC_BASE_ADDR + TOP_DARJEELING_MBX1_SOC_SIZE_BYTES`.
 */
#define TOP_DARJEELING_MBX1_SOC_SIZE_BYTES 0x20
/**
 * Peripheral base address for soc device on mbx2 in top darjeeling.
 *
 * This should be used with #mmio_region_from_addr to access the memory-mapped
 * registers associated with the peripheral (usually via a DIF).
 */
#define TOP_DARJEELING_MBX2_SOC_BASE_ADDR 0x1465200

/**
 * Peripheral size for soc device on mbx2 in top darjeeling.
 *
 * This is the size (in bytes) of the peripheral's reserved memory area. All
 * memory-mapped registers associated with this peripheral should have an
 * address between #TOP_DARJEELING_MBX2_SOC_BASE_ADDR and
 * `TOP_DARJEELING_MBX2_SOC_BASE_ADDR + TOP_DARJEELING_MBX2_SOC_SIZE_BYTES`.
 */
#define TOP_DARJEELING_MBX2_SOC_SIZE_BYTES 0x20
/**
 * Peripheral base address for soc device on mbx3 in top darjeeling.
 *
 * This should be used with #mmio_region_from_addr to access the memory-mapped
 * registers associated with the peripheral (usually via a DIF).
 */
#define TOP_DARJEELING_MBX3_SOC_BASE_ADDR 0x1465300

/**
 * Peripheral size for soc device on mbx3 in top darjeeling.
 *
 * This is the size (in bytes) of the peripheral's reserved memory area. All
 * memory-mapped registers associated with this peripheral should have an
 * address between #TOP_DARJEELING_MBX3_SOC_BASE_ADDR and
 * `TOP_DARJEELING_MBX3_SOC_BASE_ADDR + TOP_DARJEELING_MBX3_SOC_SIZE_BYTES`.
 */
#define TOP_DARJEELING_MBX3_SOC_SIZE_BYTES 0x20
/**
 * Peripheral base address for soc device on mbx4 in top darjeeling.
 *
 * This should be used with #mmio_region_from_addr to access the memory-mapped
 * registers associated with the peripheral (usually via a DIF).
 */
#define TOP_DARJEELING_MBX4_SOC_BASE_ADDR 0x1465400

/**
 * Peripheral size for soc device on mbx4 in top darjeeling.
 *
 * This is the size (in bytes) of the peripheral's reserved memory area. All
 * memory-mapped registers associated with this peripheral should have an
 * address between #TOP_DARJEELING_MBX4_SOC_BASE_ADDR and
 * `TOP_DARJEELING_MBX4_SOC_BASE_ADDR + TOP_DARJEELING_MBX4_SOC_SIZE_BYTES`.
 */
#define TOP_DARJEELING_MBX4_SOC_SIZE_BYTES 0x20
/**
 * Peripheral base address for soc device on mbx5 in top darjeeling.
 *
 * This should be used with #mmio_region_from_addr to access the memory-mapped
 * registers associated with the peripheral (usually via a DIF).
 */
#define TOP_DARJEELING_MBX5_SOC_BASE_ADDR 0x1465500

/**
 * Peripheral size for soc device on mbx5 in top darjeeling.
 *
 * This is the size (in bytes) of the peripheral's reserved memory area. All
 * memory-mapped registers associated with this peripheral should have an
 * address between #TOP_DARJEELING_MBX5_SOC_BASE_ADDR and
 * `TOP_DARJEELING_MBX5_SOC_BASE_ADDR + TOP_DARJEELING_MBX5_SOC_SIZE_BYTES`.
 */
#define TOP_DARJEELING_MBX5_SOC_SIZE_BYTES 0x20
/**
 * Peripheral base address for soc device on mbx6 in top darjeeling.
 *
 * This should be used with #mmio_region_from_addr to access the memory-mapped
 * registers associated with the peripheral (usually via a DIF).
 */
#define TOP_DARJEELING_MBX6_SOC_BASE_ADDR 0x1465600

/**
 * Peripheral size for soc device on mbx6 in top darjeeling.
 *
 * This is the size (in bytes) of the peripheral's reserved memory area. All
 * memory-mapped registers associated with this peripheral should have an
 * address between #TOP_DARJEELING_MBX6_SOC_BASE_ADDR and
 * `TOP_DARJEELING_MBX6_SOC_BASE_ADDR + TOP_DARJEELING_MBX6_SOC_SIZE_BYTES`.
 */
#define TOP_DARJEELING_MBX6_SOC_SIZE_BYTES 0x20
/**
 * Peripheral base address for soc device on mbx_pcie0 in top darjeeling.
 *
 * This should be used with #mmio_region_from_addr to access the memory-mapped
 * registers associated with the peripheral (usually via a DIF).
 */
#define TOP_DARJEELING_MBX_PCIE0_SOC_BASE_ADDR 0x1460100

/**
 * Peripheral size for soc device on mbx_pcie0 in top darjeeling.
 *
 * This is the size (in bytes) of the peripheral's reserved memory area. All
 * memory-mapped registers associated with this peripheral should have an
 * address between #TOP_DARJEELING_MBX_PCIE0_SOC_BASE_ADDR and
 * `TOP_DARJEELING_MBX_PCIE0_SOC_BASE_ADDR + TOP_DARJEELING_MBX_PCIE0_SOC_SIZE_BYTES`.
 */
#define TOP_DARJEELING_MBX_PCIE0_SOC_SIZE_BYTES 0x20
/**
 * Peripheral base address for soc device on mbx_pcie1 in top darjeeling.
 *
 * This should be used with #mmio_region_from_addr to access the memory-mapped
 * registers associated with the peripheral (usually via a DIF).
 */
#define TOP_DARJEELING_MBX_PCIE1_SOC_BASE_ADDR 0x1460200

/**
 * Peripheral size for soc device on mbx_pcie1 in top darjeeling.
 *
 * This is the size (in bytes) of the peripheral's reserved memory area. All
 * memory-mapped registers associated with this peripheral should have an
 * address between #TOP_DARJEELING_MBX_PCIE1_SOC_BASE_ADDR and
 * `TOP_DARJEELING_MBX_PCIE1_SOC_BASE_ADDR + TOP_DARJEELING_MBX_PCIE1_SOC_SIZE_BYTES`.
 */
#define TOP_DARJEELING_MBX_PCIE1_SOC_SIZE_BYTES 0x20

/**
 * MMIO Region
 *
 * MMIO region excludes any memory that is separate from the module
 * configuration space, i.e. ROM, main SRAM, and flash are excluded but
 * retention SRAM, spi_device memory, or usbdev memory are included.
 */
#define TOP_DARJEELING_MMIO_BASE_ADDR 0x1460100
#define TOP_DARJEELING_MMIO_SIZE_BYTES 0x5520

#endif  // __ASSEMBLER__

#endif  // OPENTITAN_HW_TOP_DARJEELING_SW_AUTOGEN_TOP_DARJEELING_SOC_MBX_MEMORY_H_
