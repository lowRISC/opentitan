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

plics = lib.find_modules(top['module'], 'rv_plic')
has_plic = any(addr_space in plic['base_addrs'][None] for plic in plics)
plics = [x["name"] for x in plics]
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
%   for plic in plics:

/**
 * PLIC Interrupt Source to Peripheral Map
 *
 * This array is a mapping from `${helper.plic_interrupts[plic].name.as_c_type()}` to
 * `${helper.plic_sources[plic].name.as_c_type()}`.
 */
${helper.plic_mapping[plic].render_definition()}
% endfor
%endif
