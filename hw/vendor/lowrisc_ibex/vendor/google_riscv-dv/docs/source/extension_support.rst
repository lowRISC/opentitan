Extension Support
=================

Bit Manipulation Extension
--------------------------------------------------------
Setup RISCV-GCC compiler toolchain and ISS simulator
--------------------------------------------------------

1. Install `riscv-gcc`_ toolchain

  - Download the repo and add " --enable-commitlog" at the end of line 6 in
    `build_file`_ as it's not enabled by default
  - Follow the `steps`_ to install GCC and spike

2.  Update environment variable RISCV_GCC to the RISC-V gcc executable
    executable. (example: <install_dir>/bin/riscv64-unknown-elf-gcc)
3.  Update environment variable RISCV_OBJCOPY to RISC-V objcopy executable
    executable. (example: <install_dir>/bin/riscv64-unknown-elf-objcopy)
4.  Update environment variable SPIKE_PATH to the directory of the spike binary
5.  Update `riscv-ovpsim`_ to Nov 26, 2019 or later version

.. _steps: https://github.com/riscv/riscv-bitmanip/tree/master/tools#building-tools-with-draft-b-extension-instructions-support
.. _riscv-gcc: https://github.com/riscv/riscv-bitmanip
.. _build_file: https://github.com/riscv/riscv-bitmanip/blob/master/tools/riscv-isa-sim-build.sh
.. _riscv-ovpsim: https://github.com/riscv/riscv-ovpsim

Sample .bashrc setup::

    export RISCV_TOOLCHAIN=<riscv_gcc_install_path>
    export RISCV_GCC="$RISCV_TOOLCHAIN/bin/riscv64-unknown-elf-gcc"
    export RISCV_OBJCOPY="$RISCV_TOOLCHAIN/bin/riscv64-unknown-elf-objcopy"
    export SPIKE_PATH="$RISCV_TOOLCHAIN/bin"

Run bitmanip simulation
------------------------

Bit manipulation tests are added in target "rv32imcb" or "rv64imcb". Here is the
example to run bitmanip test with both ISS (spike and ovpsim). The instruction
trace from these ISS will be cross compared::

    run --target rv32imcb --test riscv_b_ext_test --iss spike,ovpsim

In `bitmanip testlist`_, there are a few bitmanip tests. Run option
"+enable_b_extension=1" enables it and "+enable_bitmanip_groups=zbb,zbt"
allows user to only enable one or some groups of bit manipulation instructions.

.. _bitmanip testlist: https://github.com/google/riscv-dv/blob/master/target/rv32imcb/testlist.yaml

Functional Coverage Support For Bitmanip
-----------------------------------------

The functional covergroup is defined in `riscv_instr_cover_group.sv`_.
It includes below major categories:

- If the operand is a register, cover all possible reg values for each operand::

    cp_rs1 : coverpoint instr.rs1;
    cp_rs2 : coverpoint instr.rs2;
    cp_rd  : coverpoint instr.rd;

- If the operand is an integer value and the amount of these possible values is
  less than XLEN*2, cover all the values::

    // Cover all the count values of leading/Trailing zeros (0:XLEN-1) for clz, ctz
    `B_R_INSTR_NO_RS2_CG_BEGIN(clz)
      `CP_VALUE_RANGE(num_leading_zeros, instr.rd_value, 0, XLEN-1)
    `CG_END

    // Cover all the shift values (0:XLEN-1) for slo
    `B_R_INSTR_CG_BEGIN(slo)
      `CP_VALUE_RANGE(num_ones_shift, instr.rs2_value, 0, XLEN-1)
    `CG_END

- Hazard conditions

Before this `issue`_ is resolved, functional coverage can only be run with OVPsim::

  cov --dir out/ovpsim_sim --iss ovpsim --target rv32imc


.. _riscv_instr_cover_group.sv: https://github.com/google/riscv-dv/blob/master/src/riscv_instr_cover_group.sv
.. _issue: https://github.com/riscv/riscv-bitmanip/issues/60
