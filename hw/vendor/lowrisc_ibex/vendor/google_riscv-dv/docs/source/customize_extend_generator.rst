Customize and Extend Generator
==============================

Add custom instructions
-----------------------

1. Add the new instruction enum to `riscv_custom_instr_enum.sv`_

.. code-block:: verilog

    CUSTOM_ADD,
    CUSTOM_SUB,
    ...

2. Add custom instruction definition to `rv32x_instr.sv`_/`rv64x_instr.sv`_

.. code-block:: verilog

    `DEFINE_CUSTOM_INSTR(CUSTOM_ADD, R_FORMAT, ARITHMETIC, RV32X)
    `DEFINE_CUSTOM_INSTR(CUSTOM_SUB, R_FORMAT, ARITHMETIC, RV32X)
    ...

3. Extend `riscv_custom_instr.sv`_ and implement key functions like get_instr_name, convert2asm
4. Add RV32X/RV64X to supported_isa in riscv_core_setting.sv

.. _riscv_custom_instr_enum.sv: https://github.com/google/riscv-dv/blob/master/src/isa/custom/riscv_custom_instr_enum.sv
.. _riscv_custom_instr.sv: https://github.com/google/riscv-dv/blob/master/src/isa/custom/riscv_custom_instr.sv
.. _rv32x_instr.sv: https://github.com/google/riscv-dv/blob/master/src/isa/custom/rv32x_instr.sv
.. _rv64x_instr.sv: https://github.com/google/riscv-dv/blob/master/src/isa/custom/rv64x_instr.sv
