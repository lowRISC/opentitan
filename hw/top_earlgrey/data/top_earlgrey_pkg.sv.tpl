// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

<%
import topgen.lib as lib


def camelcase(str):
    """Turns a string from 'snake_case' to 'CamelCase'."""
    return "".join([part.capitalize() for part in str.split("_")])


def get_dio_pin_enum_literal(sig, start_idx):
    """Returns the DIO pin enum literal with value assignment"""
    if "width" in sig and sig["width"] > 1:
        return camelcase("top_{}_dio_pin_{}_[{}] = {}".format(
            top["name"], sig["name"], int(sig["width"]), start_idx))
    else:
        return camelcase("top_{}_dio_pin_{} = {}".format(
            top["name"], sig["name"], start_idx))
%>\
package top_${top["name"]}_pkg;

  // Base addresses of all peripherals.
  % for m in top["module"]:
  ${"parameter TOP_{}_{}_BASE_ADDR = 32'h{}".format(top["name"].upper(),
                                                    m["name"].upper(),
                                                    m["base_addr"][2:])};
  % endfor

  // Enumeration for DIO pins.
  typedef enum {
  <% pin_cnt = 0 %>\
  % for sig in reversed(top["pinmux"]["dio"]):
  ${get_dio_pin_enum_literal(sig, pin_cnt)},
  <% pin_cnt += int(sig["width"]) if "width" in sig else 1 %>\
  % endfor
  ${camelcase("top_{}_dio_pin_count".format(top["name"]))} = ${pin_cnt}
  } top_${top["name"]}_dio_pin_e;

  // TODO: Enumeration for PLIC Interrupt source peripheral.
  // TODO: Enumeration for PLIC Interrupt Ids.

endpackage
