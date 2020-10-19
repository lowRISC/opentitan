// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef _TOP_${top["name"].upper()}_H_
#define _TOP_${top["name"].upper()}_H_

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

#define PINMUX_PERIPH_INSEL_IDX_OFFSET 2

// PERIPH_INSEL ranges from 0 to NUM_MIO + 2 -1}
//  0 and 1 are tied to value 0 and 1
#define NUM_MIO ${top["pinmux"]["num_mio"]}
#define NUM_DIO ${sum([x["width"] if "width" in x else 1 for x in top["pinmux"]["dio"]])}

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

// Header Extern Guard
#ifdef __cplusplus
}  // extern "C"
#endif

#endif  // _TOP_${top["name"].upper()}_H_
