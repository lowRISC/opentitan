// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
${gencmd}
<%
import topgen.lib as lib


def camelcase(str):
    """Turns a string from 'snake_case' to 'CamelCase'."""
    return "".join([part.capitalize() for part in str.split("_")])


def get_dio_pin_enum_literal(sig, start_idx):
    """Returns the DIO pin enum literal with value assignment"""
    if "width" in sig and sig["width"] > 1:
        return_str = ""
        for i in range(int(sig["width"])):
            if i > 0:
              return_str += "\n    "
            return_str += camelcase("top_{}_dio_pin_{}_{} = {},".format(
            top["name"], sig["name"], i, start_idx + i))
        return return_str
    return camelcase("top_{}_dio_pin_{} = {},".format(
        top["name"], sig["name"], start_idx))

top_name = top["name"]

%>\
package top_${top_name}_pkg;
% for (inst_name, if_name), region in helper.devices():
<%
    if_desc = inst_name if if_name is None else '{} device on {}'.format(if_name, inst_name)
    hex_base_addr = "32'h{:X}".format(region.base_addr)
    hex_size_bytes = "32'h{:X}".format(region.size_bytes)
%>\
  /**
   * Peripheral base address for ${if_desc} in top ${top_name}.
   */
  parameter int unsigned ${region.base_addr_name().as_c_define()} = ${hex_base_addr};

  /**
   * Peripheral size in bytes for ${if_desc} in top ${top_name}.
   */
  parameter int unsigned ${region.size_bytes_name().as_c_define()} = ${hex_size_bytes};

% endfor
% for name, region in helper.memories():
<%
    hex_base_addr = "32'h{:x}".format(region.base_addr)
    hex_size_bytes = "32'h{:x}".format(region.size_bytes)
%>\
  /**
   * Memory base address for ${name} in top ${top_name}.
   */
  parameter int unsigned ${region.base_addr_name().as_c_define()} = ${hex_base_addr};

  /**
   * Memory size for ${name} in top ${top_name}.
   */
  parameter int unsigned ${region.size_bytes_name().as_c_define()} = ${hex_size_bytes};

% endfor
  // Enumeration for DIO pins.
  typedef enum {
  <% pin_cnt = 0 %>\
  % for sig in reversed(top["pinmux"]["dio"]):
  ${get_dio_pin_enum_literal(sig, pin_cnt)}
  <% pin_cnt += int(sig["width"]) if "width" in sig else 1 %>\
  % endfor
  ${camelcase("top_{}_dio_pin_count".format(top_name))} = ${pin_cnt}
  } top_${top_name}_dio_pin_e;

  // TODO: Enumeration for PLIC Interrupt source peripheral.
  // TODO: Enumeration for PLIC Interrupt Ids.

endpackage
