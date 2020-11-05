End to End Simulation Flow
==========================

We have collaborated with lowRISC to apply this flow for `Ibex RISC-V core verification`_.
You can use it as a reference to setup end-to-end co-simulation flow.
This repo is still under active development, this is the recommended approach to
customize the instruction generator while keeping the effort of merging
upstream changes to a minimum.

1.  Do not modify the upstream classes directly. When possible, extend from
    the upstream classses and implement your own functionalities.

2.  Add your extensions under user_extension directory, and add the files to
    user_extension/user_extension.svh. If you prefer to put your extensions in a
    different directory, you can use "-ext <user_extension_path>" to override the
    user extension path.

3.  Create a new target directory and customize the setting and testlist

4.  Run the generator with ``--custom_target <target_dir> --isa <isa> --mabi <mabi>``

5.  Use command line type override to use your extended classes.
    ``--sim_opts="+uvm_set_type_override=<upstream_class>,<extended_class>"``

6.  If extending ``riscv_asm_program_gen`` class is desired, must use this command
    line override:
    ``--sim_opts="+uvm_set_inst_override=riscv_asm_program_gen,<extended
    class>,'uvm_test_top.asm_gen'"``

You can refer to `riscv-dv extension for Ibex`_ for a working example.

We have plan to open-source the end-to-end environments of other advanced RISC-V
processors. Stay tuned!

.. _Ibex RISC-V core verification: https://github.com/lowRISC/ibex/blob/master/doc/03_reference/verification.rst
.. _riscv-dv extension for Ibex: https://github.com/lowRISC/ibex/blob/master/dv/uvm/core_ibex/Makefile#L110




