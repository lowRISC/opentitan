/* Copyright lowRISC contributors. */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */
<%!
# TODO(#4709): Remove this function, once the old way of defining memories has been deprecated.
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

def flags(mem):
    swaccess = mem["swaccess"]
    exec = mem["exec"]
    sw_to_flags = {
        'rw': 'rw',
        'ro': 'r'
    }
    assert swaccess in sw_to_flags

    flags_str = sw_to_flags[swaccess]
    if exec:
        flags_str += "x"

    return flags_str

def get_virtual_memory_size(top):
    for mod in top["module"]:
        if "memory" in mod:
            for _, mem in mod["memory"].items():
                if mem["label"] == "eflash":
                    return hex(int(mem["size"], 0) // 2)
    return None
%>\

/**
 * Partial linker script for chip memory configuration.
 * rom_ext_virtual and owner_virtual are address windows that provide a fixed translation
 * address for whichever half of the flash contains the corresponding boot stage.
 */
MEMORY {
% for m in top["module"]:
  % if "memory" in m:
    % for key, mem in m["memory"].items():
  ${mem["label"]}(${flags(mem)}) : ORIGIN = ${m["base_addrs"][key]}, LENGTH = ${mem["size"]}
    % endfor
  % endif
% endfor
% for m in top["memory"]:
  ${m["name"]}(${memory_to_flags(m)}) : ORIGIN = ${m["base_addr"]}, LENGTH = ${m["size"]}
% endfor
  rom_ext_virtual(rx) : ORIGIN = 0x90000000, LENGTH = ${get_virtual_memory_size(top)}
  owner_virtual(rx) : ORIGIN = 0xa0000000, LENGTH = ${get_virtual_memory_size(top)}
}

/**
 * Stack at the top of the main SRAM.
 */
_stack_size = 16384;
_stack_end = ORIGIN(ram_main) + LENGTH(ram_main);
_stack_start = _stack_end - _stack_size;

/**
 * Size of the `.static_critical` section at the bottom of the main SRAM (in
 * bytes).
 */
_static_critical_size = 8136;

/**
 * `.chip_info` at the top of ROM.
 */
_chip_info_size = 128;
_chip_info_end   = ORIGIN(rom) + LENGTH(rom);
_chip_info_start = _chip_info_end - _chip_info_size;

/**
 * Size of the initial ePMP RX region at reset (in bytes). This region must be
 * large enough to cover the .crt section.
 *
 * NOTE: This value must match the size of the RX region in
 * hw/ip/rv_core_ibex/rtl/ibex_pmp_reset.svh.
 */
_epmp_reset_rx_size = 2048;
