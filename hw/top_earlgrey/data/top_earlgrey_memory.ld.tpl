/* Copyright lowRISC contributors. */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */
<%!
def memory_type_to_flags(memory_type):
    if memory_type == "rom":
        return "rx"
    elif memory_type == "eflash":
        return "rx"
    elif memory_type.startswith("ram"):
        return "w"
    else:
        return ""
%>\

/**
 * Partial linker script for chip memory configuration.
 */
MEMORY {
% for m in top["memory"]:
  ${m["name"]}(${memory_type_to_flags(m["type"])}) : ORIGIN = ${m["base_addr"]}, LENGTH = ${m["size"]}
% endfor
}
