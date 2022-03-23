// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef ${helper.header_macro_prefix}_TOP_${top["name"].upper()}_MEMORY_H_
#define ${helper.header_macro_prefix}_TOP_${top["name"].upper()}_MEMORY_H_

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


% for m in top["module"]:
  % if "memory" in m:
    % for key, val in m["memory"].items():
/**
 * Memory base for ${m["name"]}_${val["label"]} in top ${top["name"]}.
 */
#define TOP_${top["name"].upper()}_${val["label"].upper()}_BASE_ADDR ${m["base_addrs"][key]}

/**
 * Memory size for ${m["name"]}_${val["label"]} in top ${top["name"]}.
 */
#define TOP_${top["name"].upper()}_${val["label"].upper()}_SIZE_BYTES ${val["size"]}

    % endfor
  % endif
% endfor

% for m in top["memory"]:
/**
 * Memory base address for ${m["name"]} in top ${top["name"]}.
 */
#define TOP_${top["name"].upper()}_${m["name"].upper()}_BASE_ADDR ${m["base_addr"]}

/**
 * Memory size for ${m["name"]} in top ${top["name"]}.
 */
#define TOP_${top["name"].upper()}_${m["name"].upper()}_SIZE_BYTES ${m["size"]}

% endfor

% for (inst_name, if_name), region in helper.devices():
<%
    if_desc = inst_name if if_name is None else '{} device on {}'.format(if_name, inst_name)
    hex_base_addr = "0x{:X}".format(region.base_addr)
    base_addr_name = region.base_addr_name().as_c_define()
%>\
/**
 * Peripheral base address for ${if_desc} in top ${top["name"]}.
 *
 * This should be used with #mmio_region_from_addr to access the memory-mapped
 * registers associated with the peripheral (usually via a DIF).
 */
#define ${base_addr_name} ${hex_base_addr}
% endfor
#endif  // __ASSEMBLER__

#endif  // ${helper.header_macro_prefix}_TOP_${top["name"].upper()}_MEMORY_H_
