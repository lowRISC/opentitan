// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
${gencmd}
<%
import topgen.lib as lib

alert_handler = lib.find_module(top['module'], 'alert_handler')
if alert_handler is not None:
    has_alert_handler = addr_space in alert_handler['base_addrs'][None]
else:
    has_alert_handler = False

plic = lib.find_module(top['module'], 'rv_plic')
if plic is not None:
    has_plic = addr_space in plic['base_addrs'][None]
else:
    has_plic = False
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
% if has_plic:

/**
 * PLIC Interrupt Source to Peripheral Map
 *
 * This array is a mapping from `${helper.plic_interrupts.name.as_c_type()}` to
 * `${helper.plic_sources.name.as_c_type()}`.
 */
${helper.plic_mapping.render_definition()}
%endif
