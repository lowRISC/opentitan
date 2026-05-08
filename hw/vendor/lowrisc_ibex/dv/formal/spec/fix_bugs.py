# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# Original author: Louis-Emile Ploix
# SPDX-License-Identifier: Apache-2.0

'''
Fixes an issue where the Sail -> SV compiler references t_Pmpcfg_ent (in sail_genlib_ibexspec.sv) before it defines it (in ibexspec.sv)
by just moving that definition, as well as various other nit picks we can change in the specification.

Ideally the sail compiler would do all of this.
'''

from pathlib import Path

S = """
typedef struct {
    logic [7:0] bits;
} t_Pmpcfg_ent;
"""

T = """
typedef logic [127:0] sail_int;
"""

c = Path("build/ibexspec.sv").read_text()

c = c.replace(S, "")
c = c.replace("struct {", "struct packed {")
c = c.replace("sail_return = sail_internal_pick(zz498);", "/* removed */")
c = c.replace("sail_return = sail_internal_pick(zz495);", "/* removed */")
c = c.replace("        main_result = main(insn_bits, mode);", """\
        wX_sail_invoke_arg_0[0] = 0; wX_sail_invoke_arg_1[0] = 0;
        write_ram_sail_invoke_arg_0[0] = Write_plain; write_ram_sail_invoke_arg_0[1] = Write_plain;
        write_ram_sail_invoke_arg_1[0] = 0; write_ram_sail_invoke_arg_1[1] = 0;
        write_ram_sail_invoke_arg_2[0] = 0; write_ram_sail_invoke_arg_2[1] = 0;
        write_ram_sail_invoke_arg_3[0] = 0; write_ram_sail_invoke_arg_3[1] = 0;
        read_ram_sail_invoke_arg_0[0] = Read_plain; read_ram_sail_invoke_arg_0[1] = Read_plain;
        read_ram_sail_invoke_arg_1[0] = 0; read_ram_sail_invoke_arg_1[1] = 0;
        sail_reached_unreachable_loc = 0;
        main_result = main(insn_bits, mode); \
""")
c = c.replace("sail_reached_unreachable = 1;", "if (!sail_reached_unreachable) begin sail_reached_unreachable = 1; sail_reached_unreachable_loc = `__LINE__; end")
c = c.replace("module sail_ibexspec(", "module sail_ibexspec(\n    output logic sail_reached_unreachable,\n    output logic [31:0] sail_reached_unreachable_loc,")
c = c.replace("logic sail_reached_unreachable;", "")
c = c.replace("logic [31:0] sail_reached_unreachable_loc;", "")

Path("build/ibexspec.sv").write_text(c)

c = Path("build/sail_genlib_ibexspec.sv").read_text()
Path("build/sail_genlib_ibexspec.sv").write_text(S.replace("struct", "struct packed") + "\n" + c)
