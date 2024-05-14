// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

<%
    if helper.addr_space == helper.default_addr_space:
        header_suffix = top["name"].upper()
    else:
        header_suffix = "_".join([top["name"], helper.addr_space]).upper()
%>\
#ifndef ${helper.header_macro_prefix}_TOP_${header_suffix}_MEMORY_H_
#define ${helper.header_macro_prefix}_TOP_${header_suffix}_MEMORY_H_

## TODO(opentitan-integrated/issues/332): Remove this workaround
## once SW has been refactored to work without flash_ctrl.
## TODO(opentitan-integrated/issues/145): Remove this workaround
## once SW has been refactored to work without keymgr_dpe.
% if top["name"] == 'darjeeling':
#include "top_darjeeling_flash_ctrl_dummy.h"
#include "top_darjeeling_keymgr_dummy.h"

% endif
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


% for name, region in helper.memories():
<%
    hex_base_addr = "0x{:X}".format(region.base_addr)
    hex_size_bytes = "0x{:X}".format(region.size_bytes)

    base_addr_name = region.base_addr_name().as_c_define()
    size_bytes_name = region.size_bytes_name().as_c_define()

%>\
/**
 * Memory base address for ${name} in top ${top["name"]}.
 */
#define ${base_addr_name} ${hex_base_addr}

/**
 * Memory size for ${name} in top ${top["name"]}.
 */
#define ${size_bytes_name} ${hex_size_bytes}

## TODO: we need a more holistic approach to declare memories and IPs sitting in the
## CTN address space. For now, we create the base and offset for the CTN SRAM with this workaround.
% if name == "ctn":
<%
    hex_base_addr = "0x{:X}".format(region.base_addr + 0x01000000)
    hex_size_bytes = "0x{:X}".format(0x00100000)

    base_addr_name = region.base_addr_name().as_c_define().replace('CTN', 'RAM_CTN')
    size_bytes_name = region.size_bytes_name().as_c_define().replace('CTN', 'RAM_CTN')

%>\
/**
 * Memory base address for ram_ctn in top ${top["name"]}.
 */
#define ${base_addr_name} ${hex_base_addr}

/**
 * Memory size for ram_ctn in top ${top["name"]}.
 */
#define ${size_bytes_name} ${hex_size_bytes}
% endif
% endfor

% for (inst_name, if_name), region in helper.devices():
<%
    if_desc = inst_name if if_name is None else '{} device on {}'.format(if_name, inst_name)
    hex_base_addr = "0x{:X}".format(region.base_addr)
    hex_size_bytes = "0x{:X}".format(region.size_bytes)

    base_addr_name = region.base_addr_name().as_c_define()
    size_bytes_name = region.size_bytes_name().as_c_define()
%>\
/**
 * Peripheral base address for ${if_desc} in top ${top["name"]}.
 *
 * This should be used with #mmio_region_from_addr to access the memory-mapped
 * registers associated with the peripheral (usually via a DIF).
 */
#define ${base_addr_name} ${hex_base_addr}

/**
 * Peripheral size for ${if_desc} in top ${top["name"]}.
 *
 * This is the size (in bytes) of the peripheral's reserved memory area. All
 * memory-mapped registers associated with this peripheral should have an
 * address between #${base_addr_name} and
 * `${base_addr_name} + ${size_bytes_name}`.
 */
#define ${size_bytes_name} ${hex_size_bytes}
% endfor

/**
 * MMIO Region
 *
 * MMIO region excludes any memory that is separate from the module
 * configuration space, i.e. ROM, main SRAM, and flash are excluded but
 * retention SRAM, spi_device memory, or usbdev memory are included.
 */
#define ${helper.mmio.base_addr_name().as_c_define()} ${"0x{:X}".format(helper.mmio.base_addr)}
#define ${helper.mmio.size_bytes_name().as_c_define()} ${"0x{:X}".format(helper.mmio.size_bytes)}

#endif  // __ASSEMBLER__

#endif  // ${helper.header_macro_prefix}_TOP_${header_suffix}_MEMORY_H_
