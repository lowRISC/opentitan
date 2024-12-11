// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
${gencmd}
<%
import topgen.lib as lib

has_alert_handler = lib.find_module(top['module'], 'alert_handler') or top['name'] == 'englishbreakfast'
%>\

#include "${helper.header_path}"
% if has_alert_handler:

/**
 * Alert Handler Alert Source to Peripheral Map
 *
 * This array is a mapping from `${helper.alert_alerts.name.as_c_type()}` to
 * `${helper.alert_sources.name.as_c_type()}`.
 */
${helper.alert_mapping.render_definition()}
% endif

/**
 * PLIC Interrupt Source to Peripheral Map
 *
 * This array is a mapping from `${helper.plic_interrupts.name.as_c_type()}` to
 * `${helper.plic_sources.name.as_c_type()}`.
 */
${helper.plic_mapping.render_definition()}