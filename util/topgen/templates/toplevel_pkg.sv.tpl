// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
${gencmd}
<%
import topgen.lib as lib
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

% endfor

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

  // TODO: Enumeration for PLIC Interrupt source peripheral.
  // TODO: Enumeration for PLIC Interrupt Ids.

endpackage
