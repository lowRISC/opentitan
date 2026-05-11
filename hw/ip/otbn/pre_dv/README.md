# `otbn_sec_add` Verilator Testbench

This directory contains a C++ Verilator testbench for `otbn_sec_add`, the first-order masked parallel prefix adder used in the OTBN mask accelerator.
The testbench drives random two-share Boolean inputs and fresh randomness for 1 000 000 stimulus/check pairs, unmasking both input shares and the output shares to verify that the adder computes the correct (Width+1)-bit sum.


## Prerequisites

Follow the [Verilator setup guide](../../../../doc/getting_started/setup_verilator.md).


## Building and running

All commands below are run from the OpenTitan repository root.

1. Elaborate the RTL and compile the Verilated model.
   ```sh
   verilator --cc --exe --build --trace --assert -Wno-WIDTH \
     --top-module otbn_sec_add \
     -GWidth=32 \
     -CFLAGS "-DWIDTH=32" \
     +define+INC_ASSERT -UVERILATOR \
     -Ihw/ip/prim/rtl \
     -Ihw/ip/prim_generic/rtl \
     hw/ip/prim/rtl/prim_secded_pkg.sv \
     hw/ip/prim/rtl/prim_trivium_pkg.sv \
     hw/ip/prim/rtl/prim_util_pkg.sv \
     hw/ip/prim/rtl/prim_mubi_pkg.sv \
     hw/ip/lc_ctrl/rtl/lc_ctrl_reg_pkg.sv \
     hw/ip/lc_ctrl/rtl/lc_ctrl_state_pkg.sv \
     hw/ip/lc_ctrl/rtl/lc_ctrl_pkg.sv \
     hw/ip/otp_ctrl/rtl/otp_ctrl_pkg.sv \
     hw/ip/otbn/rtl/otbn_pkg.sv \
     hw/ip/otbn/rtl/otbn_sec_add.sv \
     hw/ip/otbn/pre_dv/otbn_sec_add_tb.cpp \
     -o otbn_sec_add_tb
   ```


1. Run the testbench.
   ```sh
   obj_dir/otbn_sec_add_tb
   ```

   A passing run produces:
   ```
   Test ***PASSED*** 1000000 checks
   ```

   A failing run prints one line per mismatch and then:
   ```
   Test ***FAILED*** <n> / 1000000
   ```

The simulation also writes a VCD waveform to `dump.vcd` in the working directory.


## Configuring the adder width

The testbench supports Width values of 4, 8, 16, and 32 bits.
Two flags must always be kept in sync:

| Flag                  | Purpose                                              |
|-----------------------|------------------------------------------------------|
| `-GWidth=N`           | Sets the `Width` parameter of the elaborated RTL     |
| `-CFLAGS "-DWIDTH=N"` | Sets the matching `WIDTH` macro in the C++ testbench |

Mismatching the two values produces silent wrong results because the testbench and the DUT would disagree on the randomness bus width and the result layout.

Before switching to a different width, remove the stale build artefacts to avoid linker errors from a previous elaboration.

```sh
rm -rf obj_dir
```

Example for Width=16:

```sh
verilator --cc --exe --build --trace --assert -Wno-WIDTH \
  --top-module otbn_sec_add \
  -GWidth=16 \
  -CFLAGS "-DWIDTH=16" \
  +define+INC_ASSERT -UVERILATOR \
  -Ihw/ip/prim/rtl \
  -Ihw/ip/prim_generic/rtl \
  hw/ip/prim/rtl/prim_secded_pkg.sv \
  hw/ip/prim/rtl/prim_trivium_pkg.sv \
  hw/ip/prim/rtl/prim_util_pkg.sv \
  hw/ip/prim/rtl/prim_mubi_pkg.sv \
  hw/ip/lc_ctrl/rtl/lc_ctrl_reg_pkg.sv \
  hw/ip/lc_ctrl/rtl/lc_ctrl_state_pkg.sv \
  hw/ip/lc_ctrl/rtl/lc_ctrl_pkg.sv \
  hw/ip/otp_ctrl/rtl/otp_ctrl_pkg.sv \
  hw/ip/otbn/rtl/otbn_pkg.sv \
  hw/ip/otbn/rtl/otbn_sec_add.sv \
  hw/ip/otbn/pre_dv/otbn_sec_add_tb.cpp \
  -o otbn_sec_add_tb
obj_dir/otbn_sec_add_tb
```
