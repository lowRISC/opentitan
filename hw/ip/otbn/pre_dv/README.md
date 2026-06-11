# `otbn_mask_accelerator` Verilator Testbench

This directory contains C++ Verilator testbenches for modules in the OTBN mask accelerator pipeline.

- `otbn_mask_accelerator_tb.cpp` — tests `otbn_mask_accelerator`, the top-level masked operation unit.
- `otbn_sec_add_tb.cpp` — tests `otbn_sec_add`, the first-order masked parallel prefix adder.
- `otbn_tb_utils.h` — shared utilities (clock helpers, share accessors, derived constants).


## Prerequisites

Follow the [Verilator setup guide](../../../../doc/getting_started/setup_verilator.md).


## Building and running `otbn_mask_accelerator`

All commands below are run from the OpenTitan repository root.

1. Elaborate the RTL and compile the Verilated model.
   ```sh
   verilator --cc --exe --build --trace --assert -Wno-WIDTH -Wno-UNOPTFLAT \
     --top-module otbn_mask_accelerator \
     -Ihw/ip/prim/rtl \
     -Ihw/ip/prim_generic/rtl \
     hw/ip/prim/rtl/prim_secded_pkg.sv \
     hw/ip/prim/rtl/prim_trivium_pkg.sv \
     hw/ip/prim/rtl/prim_util_pkg.sv \
     hw/ip/prim/rtl/prim_mubi_pkg.sv \
     hw/ip/prim/rtl/prim_count_pkg.sv \
     hw/ip/lc_ctrl/rtl/lc_ctrl_reg_pkg.sv \
     hw/ip/lc_ctrl/rtl/lc_ctrl_state_pkg.sv \
     hw/ip/lc_ctrl/rtl/lc_ctrl_pkg.sv \
     hw/ip/otp_ctrl/rtl/otp_ctrl_pkg.sv \
     hw/ip/otbn/rtl/otbn_pkg.sv \
     hw/ip/otbn/rtl/otbn_sec_add.sv \
     hw/ip/otbn/rtl/otbn_sec_add_mod.sv \
     hw/ip/otbn/rtl/otbn_mask_accelerator.sv \
     hw/ip/prim/rtl/prim_blanker.sv \
     hw/ip/prim/rtl/prim_count.sv \
     hw/ip/prim/rtl/prim_fifo_sync.sv \
     hw/ip/prim_generic/rtl/prim_flop.sv \
     hw/ip/prim_generic/rtl/prim_flop_en.sv \
     hw/ip/otbn/pre_dv/otbn_mask_accelerator_tb.cpp \
     -o otbn_mask_accelerator_tb
   ```

   `--Wno-UNOPTFLAT` suppresses a false-positive combinational-loop warning on `pre_p` inside `otbn_sec_add`.
   Verilator 4.x traces the whole `buffer_data` array as one node and misses the register break provided by the `prim_flop_en` chain, making the pass-2 feedback path look combinational when it is not.

2. Run the testbench.
   ```sh
   obj_dir/otbn_mask_accelerator_tb
   ```

   A passing run produces:
   ```
   Mode 0 (SecAdd): PASS - 0 errors / 8000 checks
   Mode 1 (SecAddMod): PASS - 0 errors / 8000 checks
   Mode 2 (ArithToBool): PASS - 0 errors / 8000 checks
   Mode 3 (BoolToArith): PASS - 0 errors / 8000 checks
   Test ***PASSED*** all 4 modes
   ```

The simulation also writes a VCD waveform to `dump.vcd` in the working directory.


## Operation modes

The testbench exercises all four modes in a single run, in order:

| Mode | Name          | Description                                    | Output sharing |
|------|---------------|------------------------------------------------|----------------|
| 0    | `SecAdd`      | Masked addition, no modular reduction          | Boolean        |
| 1    | `SecAddMod`   | Masked modular addition                        | Boolean        |
| 2    | `ArithToBool` | Arithmetic-to-Boolean share conversion         | Boolean        |
| 3    | `BoolToArith` | Boolean-to-Arithmetic share conversion         | Arithmetic     |

Each mode runs a number of accepted vectors.
After each mode the testbench waits for `wready_o` to go high (adder idle), then issues a one-cycle pulse of `sec_wipe_running_i` to flush the pipeline before the next mode begins.


## Building and running `otbn_sec_add`

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

   `-UVERILATOR +define+INC_ASSERT` activates the full standard assertion macros and enables the `INC_ASSERT`-gated checks in `otbn_sec_add`.
   This works because `otbn_sec_add` uses only `ASSERT_INIT` and `ASSERT_FINAL` (immediate/final blocks), which Verilator 4.x supports.

2. Run the testbench.
   ```sh
   obj_dir/otbn_sec_add_tb
   ```

   A passing run produces:
   ```
   Test ***PASSED*** 1000000 checks
   ```

### Configuring the adder width

The `otbn_sec_add` testbench supports Width values of 4, 8, 16, and 32 bits.
Two flags must always be kept in sync:

| Flag                      | Purpose                                              |
|---------------------------|------------------------------------------------------|
| `-GWidth=N`               | Sets the `Width` parameter of the elaborated RTL     |
| `-CFLAGS "-DWIDTH=N ..."` | Sets the matching `WIDTH` macro in the C++ testbench |

Mismatching the two values produces wrong results because the testbench and the DUT will disagree on the randomness bus width and the result layout.

Before switching to a different width, remove the stale build artefacts to avoid linker errors from a previous elaboration:
```sh
rm -rf obj_dir
```
