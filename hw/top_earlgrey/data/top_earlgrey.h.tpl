// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef _TOP_${top["name"].upper()}_H_
#define _TOP_${top["name"].upper()}_H_

// Header Extern Guard  (so header can be used from C and C++)
#ifdef __cplusplus
extern "C" {
#endif

#define PINMUX_PERIPH_INSEL_IDX_OFFSET 2

// PERIPH_INSEL ranges from 0 to NUM_MIO + 2 -1}
//  0 and 1 are tied to value 0 and 1
#define NUM_MIO ${top["pinmux"]["num_mio"]}
#define NUM_DIO ${sum([x["width"] if "width" in x else 1 for x in top["pinmux"]["dio"]])}

<% offset = 0 %>\
% for i, sig in enumerate(top["pinmux"]["inouts"] + top["pinmux"]["inputs"]):
  % if sig["width"] == 1:
#define PINMUX_${sig["name"].upper()}_IN ${offset + i}
  % else:
    % for j in range(sig["width"]):
#define PINMUX_${sig["name"].upper()}_${j}_IN ${offset + i + j}
    % endfor
<% offset += sig["width"] %>\
  % endif
% endfor

#define PINMUX_PERIPH_OUTSEL_IDX_OFFSET 3

// PERIPH_OUTSEL ranges from 0 to NUM_MIO + 3 -1}
// 0, 1 and 2 are tied to value 0, 1 and high-impedance

## offset starts from 3 as 0, 1, 2 are prefixed value
<% offset = 3 %>\
#define PINMUX_VALUE_0_OUT 0
#define PINMUX_VALUE_1_OUT 1
#define PINMUX_VALUE_Z_OUT 2
% for i, sig in enumerate(top["pinmux"]["inouts"] + top["pinmux"]["outputs"]):
  % if sig["width"] == 1:
#define PINMUX_${sig["name"].upper()}_OUT ${offset + i}
  % else:
    % for j in range(sig["width"]):
#define PINMUX_${sig["name"].upper()}_${j}_OUT ${offset + i + j}
    % endfor
<% offset += sig["width"] %>\
  % endif
% endfor

% for name, region in helper.modules():
/**
 * Peripheral base address for ${name} in top ${top["name"]}.
 *
 * This should be used with #mmio_region_from_addr to access the memory-mapped
 * registers associated with the peripheral (usually via a DIF).
 */
#define ${region.base_addr_name().as_c_define()} ${region.base_addr}u

/**
 * Peripheral size for ${name} in top ${top["name"]}.
 *
 * This is the size (in bytes) of the peripheral's reserved memory area. All
 * memory-mapped registers associated with this peripheral should have an
 * address between #${region.base_addr_name().as_c_define()} and
 * `${region.base_addr_name().as_c_define()} + ${region.size_bytes_name().as_c_define()}`.
 */
#define ${region.size_bytes_name().as_c_define()} ${region.size_bytes}u

% endfor

% for name, region in helper.memories():
/**
 * Memory base address for ${name} in top ${top["name"]}.
 */
#define ${region.base_addr_name().as_c_define()} ${region.base_addr}u

/**
 * Memory size for ${name} in top ${top["name"]}.
 */
#define ${region.size_bytes_name().as_c_define()} ${region.size_bytes}u

% endfor

/**
 * PLIC Interrupt Source Peripheral.
 *
 * Enumeration used to determine which peripheral asserted the corresponding
 * interrupt.
 */
${helper.plic_sources.render()}

/**
 * PLIC Interrupt Source.
 *
 * Enumeration of all PLIC interrupt sources. The interrupt sources belonging to
 * the same peripheral are guaranteed to be consecutive.
 */
${helper.plic_interrupts.render()}

/**
 * PLIC Interrupt Source to Peripheral Map
 *
 * This array is a mapping from `${helper.plic_interrupts.name.as_c_type()}` to
 * `${helper.plic_sources.name.as_c_type()}`.
 */
${helper.plic_mapping.render_declaration()}

/**
 * PLIC Interrupt Target.
 *
 * Enumeration used to determine which set of IE, CC, threshold registers to
 * access for a given interrupt target.
 */
${helper.plic_targets.render()}

// Header Extern Guard
#ifdef __cplusplus
}  // extern "C"
#endif

#endif  // _TOP_${top["name"].upper()}_H_
