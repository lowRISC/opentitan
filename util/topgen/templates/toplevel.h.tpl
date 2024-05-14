// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

<%
    if helper.addr_space == helper.default_addr_space:
        header_suffix = top["name"].upper()
    else:
        header_suffix = "_".join([top["name"], helper.addr_space]).upper()
%>\
#ifndef ${helper.header_macro_prefix}_TOP_${header_suffix}_H_
#define ${helper.header_macro_prefix}_TOP_${header_suffix}_H_

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
 * @brief Top-specific Definitions
 *
 * This file contains preprocessor and type definitions for use within the
 * device C/C++ codebase.
 *
 * These definitions are for information that depends on the top-specific chip
 * configuration, which includes:
 * - Device Memory Information (for Peripherals and Memory)
 * - PLIC Interrupt ID Names and Source Mappings
 * - Alert ID Names and Source Mappings
 * - Pinmux Pin/Select Names
 * - Power Manager Wakeups
 */

#ifdef __cplusplus
extern "C" {
#endif

% for (inst_name, if_name), region in helper.devices():
<%
    if_desc = inst_name if if_name is None else '{} device on {}'.format(if_name, inst_name)
    hex_base_addr = "0x{:X}u".format(region.base_addr)
    hex_size_bytes = "0x{:X}u".format(region.size_bytes)

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

% for name, region in helper.memories():
<%
    hex_base_addr = "0x{:X}u".format(region.base_addr)
    hex_size_bytes = "0x{:X}u".format(region.size_bytes)

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
    hex_base_addr = "0x{:X}u".format(region.base_addr + 0x01000000)
    hex_size_bytes = "0x{:X}u".format(0x00100000)

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

% if helper.addr_space == helper.default_addr_space:
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

/**
 * Alert Handler Source Peripheral.
 *
 * Enumeration used to determine which peripheral asserted the corresponding
 * alert.
 */
${helper.alert_sources.render()}

/**
 * Alert Handler Alert Source.
 *
 * Enumeration of all Alert Handler Alert Sources. The alert sources belonging to
 * the same peripheral are guaranteed to be consecutive.
 */
${helper.alert_alerts.render()}

/**
 * Alert Handler Alert Source to Peripheral Map
 *
 * This array is a mapping from `${helper.alert_alerts.name.as_c_type()}` to
 * `${helper.alert_sources.name.as_c_type()}`.
 */
${helper.alert_mapping.render_declaration()}

// PERIPH_INSEL ranges from 0 to TOP_${top["name"].upper()}_NUM_MIO_PADS + 2 -1}
//  0 and 1 are tied to value 0 and 1
#define TOP_${top["name"].upper()}_NUM_MIO_PADS ${
                       top["pinmux"]["io_counts"]["muxed"]["pads"]}
#define TOP_${top["name"].upper()}_NUM_DIO_PADS ${
                       top["pinmux"]["io_counts"]["dedicated"]["inouts"] + \
                       top["pinmux"]["io_counts"]["dedicated"]["inputs"] + \
                       top["pinmux"]["io_counts"]["dedicated"]["outputs"]}

#define TOP_${top["name"].upper()}_PINMUX_MIO_PERIPH_INSEL_IDX_OFFSET 2
#define TOP_${top["name"].upper()}_PINMUX_PERIPH_OUTSEL_IDX_OFFSET 3

/**
 * Pinmux Peripheral Input.
 */
${helper.pinmux_peripheral_in.render()}

/**
 * Pinmux MIO Input Selector.
 */
${helper.pinmux_insel.render()}

/**
 * Pinmux MIO Output.
 */
${helper.pinmux_mio_out.render()}

/**
 * Pinmux Peripheral Output Selector.
 */
${helper.pinmux_outsel.render()}

/**
 * Dedicated Pad Selects
 */
${helper.direct_pads.render()}

/**
 * Muxed Pad Selects
 */
${helper.muxed_pads.render()}

/**
 * Power Manager Wakeup Signals
 */
${helper.pwrmgr_wakeups.render()}

/**
 * Reset Manager Software Controlled Resets
 */
${helper.rstmgr_sw_rsts.render()}

/**
 * Power Manager Reset Request Signals
 */
${helper.pwrmgr_reset_requests.render()}

/**
 * Clock Manager Software-Controlled ("Gated") Clocks.
 *
 * The Software has full control over these clocks.
 */
${helper.clkmgr_gateable_clocks.render()}

/**
 * Clock Manager Software-Hinted Clocks.
 *
 * The Software has partial control over these clocks. It can ask them to stop,
 * but the clock manager is in control of whether the clock actually is stopped.
 */
${helper.clkmgr_hintable_clocks.render()}
% endif

/**
 * MMIO Region
 *
 * MMIO region excludes any memory that is separate from the module
 * configuration space, i.e. ROM, main SRAM, and flash are excluded but
 * retention SRAM, spi_device memory, or usbdev memory are included.
 */
#define ${helper.mmio.base_addr_name().as_c_define()} ${"0x{:X}u".format(helper.mmio.base_addr)}
#define ${helper.mmio.size_bytes_name().as_c_define()} ${"0x{:X}u".format(helper.mmio.size_bytes)}

// Header Extern Guard
#ifdef __cplusplus
}  // extern "C"
#endif

#endif  // ${helper.header_macro_prefix}_TOP_${header_suffix}_H_
