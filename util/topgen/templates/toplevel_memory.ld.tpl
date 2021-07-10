/* Copyright lowRISC contributors. */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */
<%!
def memory_to_flags(memory):
    memory_type = memory["type"]
    memory_access = memory.get("swaccess", "rw")
    assert memory_access in ["ro", "rw"]

    flags_str = ""
    if memory_access == "ro":
        flags_str += "r"
    else:
        flags_str += "rw"

    if memory_type in ["rom", "eflash"]:
        flags_str += "x"

    return flags_str
%>\

/**
 * Partial linker script for chip memory configuration.
 * eflash virtual is a fixed address that does not physically exist but is used as the
 * translation base
 */
MEMORY {
% for m in top["module"]:
  % if "memory" in m:
    % for key, val in m["memory"].items():
  ${val["label"]}(${val["swaccess"]}) : ORIGIN = ${m["base_addrs"][key]}, LENGTH = ${val["size"]}
    % endfor
  % endif
% endfor
% for m in top["memory"]:
  ${m["name"]}(${memory_to_flags(m)}) : ORIGIN = ${m["base_addr"]}, LENGTH = ${m["size"]}
% endfor
  eflash_virtual(rx) : ORIGIN = 0x80000000, LENGTH = 0x100000
}
