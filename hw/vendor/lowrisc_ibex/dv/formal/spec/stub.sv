// Copyright lowRISC contributors.
// Copyright 2024 University of Oxford, see also CREDITS.md.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// Original author: Louis-Emile Ploix
// SPDX-License-Identifier: Apache-2.0

/*
Provides stubs (mostly) for the native functions the Sail expects to see, mostly
handling config stuff.
*/

function automatic logic[127:0] sail_emod_int(logic[127:0] x, logic[127:0] y);
    // This one is unsigned, but the rest should be signed
    return x % y;
endfunction

function automatic logic[127:0] sail_pow_int(logic[127:0] x, logic[127:0] y);
    // These are Sail integers, so operations on them should be signed
    return signed'(x) ** signed'(y);
endfunction

function automatic logic[127:0] sail_tmod_int(logic[127:0] x, logic[127:0] y);
    return signed'(x) % signed'(y);
endfunction

function automatic logic[127:0] sail_tdiv_int(logic[127:0] x, logic[127:0] y);
    return signed'(x) / signed'(y);
endfunction

function automatic sail_bits sail_shift_bits_left(sail_bits x, sail_bits y);
    return {x.size, x.bits << y.bits};
endfunction

function automatic sail_bits sail_shift_bits_right(sail_bits x, sail_bits y);
    return {x.size, x.bits >> y.bits};
endfunction

function automatic sail_unit sail_decimal_string_of_bits(logic [11:0] x);
    return SAIL_UNIT;
endfunction
function automatic logic sail_elf_tohost(sail_unit u); return 0; endfunction
function automatic logic sail_get_config_print_mem(sail_unit u); return 0; endfunction
function automatic logic sail_get_config_print_platform(sail_unit u); return 0; endfunction
function automatic logic sail_get_config_print_reg(sail_unit u); return 0; endfunction
function automatic logic sail_get_config_print_instr(sail_unit u); return 0; endfunction
function automatic logic sail_get_config_print_exception(sail_unit u); return 0; endfunction
function automatic logic[31:0] sail_plat_clint_base(sail_unit u); return 0; endfunction
function automatic logic[31:0] sail_plat_clint_size(sail_unit u); return 0; endfunction
function automatic logic sail_plat_enable_dirty_update(sail_unit u); return 0; endfunction
function automatic logic sail_plat_enable_misaligned_access(sail_unit u); return 1; endfunction
function automatic logic sail_plat_enable_pmp(sail_unit u); return 0; endfunction
function automatic sail_unit sail_platform_barrier(t_barrier_kind k); return SAIL_UNIT; endfunction
function automatic sail_unit sail_platform_write_mem_ea(
    t_write_kind a, logic [63:0] b, sail_bits c, logic [127:0] d
); return SAIL_UNIT; endfunction
function automatic logic[15:0] sail_plat_get_16_random_bits(sail_unit u); return 0; endfunction
function automatic logic sail_plat_htif_tohost(sail_unit u); return 0; endfunction
function automatic logic sail_plat_mtval_has_illegal_inst_bits(sail_unit u); return 1; endfunction
function automatic logic[31:0] sail_plat_ram_base(sail_unit u); return 0; endfunction
function automatic logic[31:0] sail_plat_ram_size(sail_unit u); return 0; endfunction
function automatic logic[31:0] sail_plat_rom_base(sail_unit u); return 0; endfunction
function automatic logic[31:0] sail_plat_rom_size(sail_unit u); return 0; endfunction
function automatic sail_unit sail_plat_term_write(logic[7:0] u); return SAIL_UNIT; endfunction
function automatic sail_unit sail_print_mem_access(sail_unit u); return SAIL_UNIT; endfunction
function automatic sail_unit sail_print_platform(sail_unit u); return SAIL_UNIT; endfunction
function automatic sail_unit sail_print_reg(sail_unit u); return SAIL_UNIT; endfunction
function automatic sail_unit sail_string_of_int(logic[127:0] u); return SAIL_UNIT; endfunction
function automatic logic sail_sys_enable_fdext(sail_unit u); return 0; endfunction
function automatic logic sail_sys_enable_rvc(sail_unit u); return 1; endfunction
function automatic logic sail_sys_enable_writable_misa(sail_unit u); return 0; endfunction
function automatic logic sail_sys_enable_zfinx(sail_unit u); return 0; endfunction
function automatic sail_unit sail_cancel_reservation(sail_unit u); return SAIL_UNIT; endfunction
function automatic logic[31:0] sail_plat_uart_base(sail_unit u); return 0; endfunction
function automatic logic[31:0] sail_plat_uart_size(sail_unit u); return 0; endfunction
function automatic logic[6:0] sail_sys_pmp_count(sail_unit u); return 7'd4; endfunction
function automatic logic[6:0] sail_sys_pmp_max_count(sail_unit u); return 7'd16; endfunction
function automatic sail_unit sail_load_reservation(logic[31:0] u); return SAIL_UNIT; endfunction
function automatic logic sail_speculate_conditional(sail_unit u); return 0; endfunction
function automatic logic[63:0] sail_sys_pmp_grain(sail_unit u); return 0; endfunction
function automatic logic sail_sys_enable_writable_fiom(sail_unit u); return 0; endfunction
