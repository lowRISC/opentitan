// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "${helper.header_path}"

% for interrupt_domain, plic_mapping in helper.plic_mapping.items():
    % if len(plic_mapping) > 1:
/**
 * PLIC Interrupt Source to Peripheral Map for the `${interrupt_domain}` domain
 *
 * This array is a mapping from `${helper.plic_interrupts[interrupt_domain].name.as_c_type()}` to
 * `${helper.plic_sources[interrupt_domain].name.as_c_type()}`.
 */
${plic_mapping.render_definition()}
    % endif
% endfor
% if helper.addr_space == helper.default_addr_space:
/**
 * Alert Handler Alert Source to Peripheral Map
 *
 * This array is a mapping from `${helper.alert_alerts.name.as_c_type()}` to
 * `${helper.alert_sources.name.as_c_type()}`.
 */
${helper.alert_mapping.render_definition()}\
% endif
