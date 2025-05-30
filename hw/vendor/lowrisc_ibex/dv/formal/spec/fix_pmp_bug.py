'''
Fixes an issue where the Sail -> SV compiler references t_Pmpcfg_ent (in sail_genlib_ibexspec.sv) before it defines it (in ibexspec.sv)
by just moving that definition.
'''

S = """
typedef struct {
    logic [7:0] bits;
} t_Pmpcfg_ent;
"""

T = """
typedef logic [127:0] sail_int;
"""

with open("build/ibexspec.sv", "r") as f:
    c = f.read()

c = c.replace(S, "")

with open("build/ibexspec.sv", "w") as f:
    f.write(c)

with open("build/sail_genlib_ibexspec.sv", "r") as f:
    c = f.read()

with open("build/sail_genlib_ibexspec.sv", "w") as f:
    f.write(S + "\n" + c)
