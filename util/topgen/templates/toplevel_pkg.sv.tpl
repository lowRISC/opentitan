// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
${gencmd}
<%
import topgen.lib as lib
import topgen.lib as lib

has_pinmux = lib.find_module(top['module'], 'pinmux')
%>\
package top_${top["name"]}_pkg;
% for (inst_name, if_name), region in helper.devices():
<%
    if_desc = inst_name if if_name is None else '{} device on {}'.format(if_name, inst_name)
    hex_base_addr = "32'h{:X}".format(region.base_addr)
    hex_size_bytes = "32'h{:X}".format(region.size_bytes)
%>\
  /**
   * Peripheral base address for ${if_desc} in top ${top["name"]}.
   */
  parameter int unsigned ${region.base_addr_name().as_c_define()} = ${hex_base_addr};

  /**
   * Peripheral size in bytes for ${if_desc} in top ${top["name"]}.
   */
  parameter int unsigned ${region.size_bytes_name().as_c_define()} = ${hex_size_bytes};

% endfor
% for name, region in helper.memories():
<%
    hex_base_addr = "32'h{:x}".format(region.base_addr)
    hex_size_bytes = "32'h{:x}".format(region.size_bytes)
%>\
  /**
   * Memory base address for ${name} in top ${top["name"]}.
   */
  parameter int unsigned ${region.base_addr_name().as_c_define()} = ${hex_base_addr};

  /**
   * Memory size for ${name} in top ${top["name"]}.
   */
  parameter int unsigned ${region.size_bytes_name().as_c_define()} = ${hex_size_bytes};
  ## TODO: we need a more holistic approach to declare memories and IPs sitting in the
  ## CTN address space. For now, we create the base and offset for the CTN SRAM with this workaround.
  % if name == "ctn":
<%
    hex_base_addr = "32'h{:x}".format(region.base_addr + 0x01000000)
    hex_size_bytes = "32'h{:x}".format(0x00100000)
    base_addr_name = region.base_addr_name().as_c_define().replace('CTN', 'RAM_CTN')
    size_bytes_name = region.size_bytes_name().as_c_define().replace('CTN', 'RAM_CTN')
%>\

  /**
  * Memory base address for ram_ctn in top ${top["name"]}.
  */
  parameter int unsigned ${base_addr_name} = ${hex_base_addr};

  /**
  * Memory size for ram_ctn in top ${top["name"]}.
  */
  parameter int unsigned ${size_bytes_name} = ${hex_size_bytes};
% endif

% endfor
% for alert_group, alert_modules in top["outgoing_alert_module"].items():
  
  // Number of ${alert_group} outgoing alerts
  parameter int unsigned NOutgoingAlerts${alert_group.capitalize()} = ${len(top['outgoing_alert'][alert_group])};

  // Number of LPGs for outgoing alert group ${alert_group}
  parameter int unsigned NOutgoingLpgs${alert_group.capitalize()} = ${len(top["outgoing_alert_lpgs"][alert_group])};
  
  // Enumeration of ${alert_group} outgoing alert modules
  typedef enum int unsigned {
% for mod in alert_modules:
    ${lib.Name.from_snake_case("top_" + top["name"] + "_alert_peripheral_" + mod).as_camel_case()} = ${loop.index},
% endfor
    ${lib.Name.from_snake_case("top_" + top["name"] + "_outgoing_alert_" + alert_group + "_peripheral_count").as_camel_case()}
  } ${"outgoing_alert_" + alert_group + "_peripheral_e"};

  // Enumeration of ${alert_group} outgoing alerts
  typedef enum int unsigned {
% for alert in top["outgoing_alert"][alert_group]:
    ${lib.Name.from_snake_case("top_" + top["name"] + "_alert_id_" + alert["name"]).as_camel_case()} = ${loop.index},
% endfor
    ${lib.Name.from_snake_case("top_" + top["name"] + "_outgoing_alert_" + alert_group + "_id_count").as_camel_case()}
  } ${"outgoing_alert_" + alert_group + "_id_e"};

  // Enumeration of ${alert_group} outgoing alerts AsyncOn configuration
  parameter logic [NOutgoingAlerts${alert_group.capitalize()}-1:0] AsyncOnOutgoingAlert${alert_group.capitalize()} = {
  % for alert in list(reversed(top["outgoing_alert"][alert_group])):
    1'b${alert['async']}${"" if loop.last else ","}
  % endfor
  };
% endfor
% for alert_group, alerts in top["incoming_alert"].items():

  // Number of ${alert_group} incoming alerts
  parameter int unsigned NIncomingAlerts${alert_group.capitalize()} = ${len(alerts)};

  // Number of LPGs for incoming alert group ${alert_group}
  parameter int unsigned NOutgoingLpgs${alert_group.capitalize()} = ${max(alert['lpg_idx'] for alert in alerts) + 1};
% endfor

  // Enumeration of alert modules
  typedef enum int unsigned {
% for mod in top["alert_module"]:
    ${lib.Name.from_snake_case("top_" + top["name"] + "_alert_peripheral_" + mod).as_camel_case()} = ${loop.index},
% endfor
    ${lib.Name.from_snake_case("top_" + top["name"] + "_alert_peripheral_count").as_camel_case()}
  } alert_peripheral_e;

  // Enumeration of alerts
  typedef enum int unsigned {
% for alert in top["alert"]:
    ${lib.Name.from_snake_case("top_" + top["name"] + "_alert_id_" + alert["name"]).as_camel_case()} = ${loop.index},
% endfor
    ${lib.Name.from_snake_case("top_" + top["name"] + "_alert_id_count").as_camel_case()}
  } alert_id_e;
% if has_pinmux:

  // Enumeration of IO power domains.
  // Only used in ASIC target.
  typedef enum logic [${len(top["pinout"]["banks"]).bit_length()-1}:0] {
% for bank in top["pinout"]["banks"]:
    ${lib.Name(['io', 'bank', bank]).as_camel_case()} = ${loop.index},
% endfor
    IoBankCount = ${len(top["pinout"]["banks"])}
  } pwr_dom_e;

  // Enumeration for MIO signals on the top-level.
  typedef enum int unsigned {
% for sig in top["pinmux"]["ios"]:
  % if sig['type'] in ['inout', 'input'] and sig['connection'] == 'muxed':
    ${lib.get_io_enum_literal(sig, 'mio_in')} = ${sig['glob_idx']},
  % endif
% endfor
<% total = top["pinmux"]['io_counts']['muxed']['inouts'] + \
           top["pinmux"]['io_counts']['muxed']['inputs'] %>\
    ${lib.Name.from_snake_case("mio_in_count").as_camel_case()} = ${total}
  } mio_in_e;

  typedef enum {
% for sig in top["pinmux"]["ios"]:
  % if sig['type'] in ['inout', 'output'] and sig['connection'] == 'muxed':
    ${lib.get_io_enum_literal(sig, 'mio_out')} = ${sig['glob_idx']},
  % endif
% endfor
<% total = top["pinmux"]['io_counts']['muxed']['inouts'] + \
           top["pinmux"]['io_counts']['muxed']['outputs'] %>\
    ${lib.Name.from_snake_case("mio_out_count").as_camel_case()} = ${total}
  } mio_out_e;

  // Enumeration for DIO signals, used on both the top and chip-levels.
  typedef enum int unsigned {
% for sig in top["pinmux"]["ios"]:
  % if sig['connection'] != 'muxed':
    ${lib.get_io_enum_literal(sig, 'dio')} = ${sig['glob_idx']},
  % endif
% endfor
<% total = top["pinmux"]['io_counts']['dedicated']['inouts'] + \
           top["pinmux"]['io_counts']['dedicated']['inputs'] + \
           top["pinmux"]['io_counts']['dedicated']['outputs'] %>\
    ${lib.Name.from_snake_case("dio_count").as_camel_case()} = ${total}
  } dio_e;

  // Enumeration for the types of pads.
  typedef enum {
    MioPad,
    DioPad
  } pad_type_e;

  // Raw MIO/DIO input array indices on chip-level.
  // TODO: Does not account for target specific stubbed/added pads.
  // Need to make a target-specific package for those.
  typedef enum int unsigned {
% for pad in top["pinout"]["pads"]:
  % if pad["connection"] == "muxed":
    ${lib.Name.from_snake_case("mio_pad_" + pad["name"]).as_camel_case()} = ${pad["idx"]},
  % endif
% endfor
    ${lib.Name.from_snake_case("mio_pad_count").as_camel_case()}
  } mio_pad_e;

  typedef enum int unsigned {
% for pad in top["pinout"]["pads"]:
  % if pad["connection"] != "muxed":
    ${lib.Name.from_snake_case("dio_pad_" + pad["name"]).as_camel_case()} = ${pad["idx"]},
  % endif
% endfor
    ${lib.Name.from_snake_case("dio_pad_count").as_camel_case()}
  } dio_pad_e;
% endif

<%
    instances = sorted(set(inst for (inst, _), __ in helper.devices()))
%>\
  // List of peripheral instantiated in this chip.
  typedef enum {
% for inst in instances:
    ${lib.Name.from_snake_case(f"peripheral_{inst}").as_camel_case()},
% endfor
    ${lib.Name.from_snake_case("peripheral_count").as_camel_case()}
  } peripheral_e;

  // TODO: Enumeration for PLIC Interrupt source peripheral.
  // TODO: Enumeration for PLIC Interrupt Ids.

// MACROs for AST analog simulation support
`ifdef ANALOGSIM
  `define INOUT_AI input ast_pkg::awire_t
  `define INOUT_AO output ast_pkg::awire_t
`else
  `define INOUT_AI inout
  `define INOUT_AO inout
`endif

endpackage
