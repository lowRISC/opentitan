# Current Verible can not support some syntax used in following files. List them here to exclude
# from Verilog style check
# tool does not support macro very well. Issue at github.com/google/verible/issues/102
riscv_instr_cover_group.sv
riscv_instr_pkg.sv
# tool does not support included file very well. Issue at github.com/google/verible/issues/178
riscv_custom_instr_enum.sv
isa/riscv_instr_cov.svh
