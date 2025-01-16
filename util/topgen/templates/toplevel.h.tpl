// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
${gencmd}
<%
import textwrap
import topgen.lib as lib

# TODO: Handle cases where there could be multiple instances of these in the
# IPs below in the design.
pwrmgr = lib.find_module(top['module'], 'pwrmgr')
if pwrmgr is not None:
    has_pwrmgr = addr_space in pwrmgr['base_addrs'][None]
else:
    has_pwrmgr = False

pinmux = lib.find_module(top['module'], 'pinmux')
if pinmux is not None:
    has_pinmux = addr_space in pinmux['base_addrs'][None]
else:
    has_pinmux = False

alert_handler = lib.find_module(top['module'], 'alert_handler')
if alert_handler is not None:
    has_alert_handler = addr_space in alert_handler['base_addrs'][None]
else:
    has_alert_handler = False

clkmgr = lib.find_module(top['module'], 'clkmgr')
if clkmgr is not None:
    has_clkmgr = addr_space in clkmgr['base_addrs'][None]
else:
    has_clkmgr = False

rstmgr = lib.find_module(top['module'], 'rstmgr')
if rstmgr is not None:
    has_rstmgr = addr_space in rstmgr['base_addrs'][None]
else:
    has_rstmgr = False

plic = lib.find_module(top['module'], 'rv_plic')
if plic is not None:
    has_plic = addr_space in plic['base_addrs'][None]
else:
    has_plic = False

addr_space_obj = lib.get_addr_space(top, addr_space)
addr_space_suffix = lib.get_addr_space_suffix(addr_space_obj)
header_suffix = (top["name"] + addr_space_suffix).upper()
%>\

#ifndef ${helper.header_macro_prefix}_TOP_${header_suffix}_H_
#define ${helper.header_macro_prefix}_TOP_${header_suffix}_H_

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
% if has_plic:
 * - PLIC Interrupt ID Names and Source Mappings
% endif
% if has_alert_handler:
 * - Alert ID Names and Source Mappings
% endif
% if has_pinmux:
 * - Pinmux Pin/Select Names
% endif
% if has_pwrmgr:
 * - Power Manager Wakeups
% endif
 */

#ifdef __cplusplus
extern "C" {
#endif

% for (inst_name, if_name), region in helper.devices(addr_space):
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

% for name, region in helper.memories(addr_space):
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

% endfor
% if has_plic:

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
% endif
% if has_alert_handler:

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
% endif
% if has_pinmux:

#define PINMUX_MIO_PERIPH_INSEL_IDX_OFFSET 2

// PERIPH_INSEL ranges from 0 to NUM_MIO_PADS + 2 -1}
//  0 and 1 are tied to value 0 and 1
#define NUM_MIO_PADS ${top["pinmux"]["io_counts"]["muxed"]["pads"]}
#define NUM_DIO_PADS ${top["pinmux"]["io_counts"]["dedicated"]["inouts"] + \
                       top["pinmux"]["io_counts"]["dedicated"]["inputs"] + \
                       top["pinmux"]["io_counts"]["dedicated"]["outputs"] }

#define PINMUX_PERIPH_OUTSEL_IDX_OFFSET 3

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
% endif
% if has_pwrmgr:

/**
 * Power Manager Wakeup Signals
 */
${helper.pwrmgr_wakeups.render()}
% endif
% if has_rstmgr:

/**
 * Reset Manager Software Controlled Resets
 */
${helper.rstmgr_sw_rsts.render()}
% endif
% if has_pwrmgr:

/**
 * Power Manager Reset Request Signals
 */
${helper.pwrmgr_reset_requests.render()}
% endif
% if has_clkmgr:

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
% for (subspace_name, description, subspace_range) in helper.subranges[addr_space]:

/**
 * ${subspace_name.upper()} Region
 *
% for l in textwrap.wrap(description, 77, break_long_words=False):
 * ${l}
% endfor
 */
#define ${subspace_range.base_addr_name().as_c_define()} ${"0x{:X}u".format(subspace_range.base_addr)}
#define ${subspace_range.size_bytes_name().as_c_define()} ${"0x{:X}u".format(subspace_range.size_bytes)}
% endfor

// Header Extern Guard
#ifdef __cplusplus
}  // extern "C"
#endif

#endif  // ${helper.header_macro_prefix}_TOP_${header_suffix}_H_
