Debug Unit plus RI5CY Testbench
=====================

This testbench tests RI5CY together with a v0.13.1 compliant [debug
unit](https://www.github.com/pulp-platform/riscv-dbg). There are several tests
that can be run, but for now it is just `riscv test_compliance` of
[riscv-openocd](https://www.github.com/riscv/riscv-openocd) (see in
`pulpissimo.cfg`) and a not yet scripted run of gdb connecting to openocd,
loading and running a hello world program (see `prog/test.c`).

You need `riscv-openocd`.

Running the testbench with vsim
----------------------
Point you environment variable `RISCV` to your RISC-V toolchain. Call `make
vsim-run` to build the testbench and the program, and run it with vsim. Use
`VSIM_FLAGS` to configure the simulator e.g. `make vsim-run VSIM_FLAGS="-gui
-debugdb"`.

Running the testbench with vcs
----------------------
Point you environment variable `RISCV` to your RISC-V toolchain. Call `make
vcs-run`. Use `VCS_FLAGS` and `SIMV_FLAGS` to configure vcs e.g. `make vcs-run
VCS_FLAGS="-debug_all"`.


Running the testbench with [verilator](https://www.veripool.org/wiki/verilator)
----------------------
Point you environment variable `RISCV` to your RISC-V toolchain. Call `make
veri-run`. Use `VERI_FLAGS` to configure verilator e.g. `make firmware-veri-run
VERI_FLAGS="+firmware=path_to_firmware +vcd"` to use a custom firmware and dump
to a vcd file.


Options
----------------------
A few plusarg options are supported.
* `+verbose` to show all memory read and writes and other miscellaneous information.

* `+vcd` to produce a vcd file called `riscy_tb.vcd`. Verilator always produces
  a vcd file called `verilator_tb.vcd`.

* `+firmware=path_to_firmware` to load a specific firmware. It is a bit tricky to
build and link your own program. Look into the `prog` folder for an example.

Example Run
-----------------------
1. `make veri-run`
3. (in new terminal) `export JTAG_VPI_PORT=port_name_from 1.`
2. (in new terminal) `openocd -f dm_compliance_test.cfg`
4. Now you can connect with gdb and interact with the testbench
