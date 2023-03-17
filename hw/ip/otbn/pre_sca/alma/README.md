# OTBN Formal Masking Verification Using Alma

This directory contains support files to formally verify the OTBN core using the
tool [Alma:
Execution-aware Masking Verification](https://github.com/IAIK/coco-alma).

## Prerequisites

Note that this flow is experimental. It has been developed using Yosys v0.15
(this also works: v0.9+4306 (git sha1 3931b3a03)), sv2v v0.0.9-24-gf868f06 and
Verilator 4.106 (2020-12-02 rev v4.106). Other tool versions might not be
compatible.

1. Download the Alma tool from this specific repo and check out to the
   `coco-otbn-latest` branch of the tool
   ```sh
   git clone git@github.com:abdullahvarici/coco-alma.git -b coco-otbn-latest
   ```
   Enter the directory using
   ```sh
   cd coco-alma
   ```
   Set up a new virtual Python environment
   ```sh
   python3 -m venv dev
   source dev/bin/activate
   ```
   And install the Python requirements
   ```sh
   pip3 install -r requirements.txt
   ```
   Update `examples/otbn/config.json` to point correct locations for `asm`,
   `objdump` and `rv_objdump`.

1. Generate a Verilog netlist

   A netlist of the DUT can be generated using the Yosys synthesis flow from
   the OpenTitan repository. From the OpenTitan top level, run
   ```sh
   cd hw/ip/otbn/pre_syn
   ```
   Set up the synthesis flow as described in the corresponding README. Then run
   the synthesis
   ```sh
   ./syn_yosys.sh
   ```

## Formally verifying the masking of the OTBN core

After downloading the Alma tool, installing dependencies and synthesizing OTBN,
the masking can finally be formally verified.

1. Enter the directory where you have downloaded Alma and load the virtual
   Python environment.
   ```sh
   source dev/bin/activate
   ```

1. Make sure to source the `build_consts.sh` script from the OpenTitan
   repository in order to set up some shell variables.
   ```sh
   source ../opentitan/util/build_consts.sh
   ```

1. Launch the Alma tool to parse, assemble, trace (simulate) and formally verify
   the netlist. For simplicity, a single script is provided to launch all the
   required steps with a single command. Simply run:
   ```sh
   ${REPO_TOP}/hw/ip/otbn/pre_sca/alma/verify_otbn.sh
   ```
   This should produce output similar to the one below:
   ```sh
   Verifying OTBN using Alma
   Starting yosys synthesis...
   | CircuitGraph | Total: 234238 | Linear: 22351 | Non-linear: 107502 | Registers: 21338 | Mux: 41352 |
   parse.py successful (755.32s)
   INSTR_LIMIT =  128
   Using program file:  programs/isw_and.S
   Using build directory: [build_directory]
   Using netlist path: ../../tmp/circuit.v
   Wrote verilator testbench to [build_directory]/verilator_tb.c
   It produces output VCD at [build_directory]/circuit.vcd
   1: Running verilator on given netlist
   2: Compiling verilated netlist library
   3: Compiling provided verilator testbench
   4: Simulating circuit and generating VCD
   Line 0: WDR label found - u_otbn_core.u_otbn_rf_bignum.gen_rf_bignum_ff.u_otbn_rf_bignum_inner.rf [7800] = secret 0
   Line 1: WDR label found - u_otbn_core.u_otbn_rf_bignum.gen_rf_bignum_ff.u_otbn_rf_bignum_inner.rf [7488] = secret 0
   Line 2: WDR label found - u_otbn_core.u_otbn_rf_bignum.gen_rf_bignum_ff.u_otbn_rf_bignum_inner.rf [7176] = secret 1
   Line 3: WDR label found - u_otbn_core.u_otbn_rf_bignum.gen_rf_bignum_ff.u_otbn_rf_bignum_inner.rf [6864] = secret 1
   Line 4: WDR label found - u_otbn_core.u_otbn_rf_bignum.gen_rf_bignum_ff.u_otbn_rf_bignum_inner.rf [6552] = static_random
   | CircuitGraph | Total: 234238 | Linear: 22351 | Non-linear: 107502 | Registers: 21338 | Mux: 41352 |
   0 nodes are ignored.
   tmp/circuit.vcd:57091: [WARNING] Entry for name clk_sys already exists in namemap (clk_sys -> #33)
   tmp/circuit.vcd:57110: [WARNING] Entry for name imem_wdata_i already exists in namemap (imem_wdata_i -> $33)
   tmp/circuit.vcd:57111: [WARNING] Entry for name imem_we_i already exists in namemap (imem_we_i -> &33)
   tmp/circuit.vcd:57112: [WARNING] Entry for name imem_wmask_i already exists in namemap (imem_wmask_i -> \'33)
   tmp/circuit.vcd:57116: [WARNING] Entry for name rst_sys_n already exists in namemap (rst_sys_n -> )33)
   Waiting for initial delay cycles:  139
   RST value:  1
   1
   Building formula for cycle 0:
   vars 0 clauses 0
   Checking cycle 0:
   Checking secret 0 [1, 2]:
   Checking secret 1 [3, 4]:
   RST value:  1
   1
   Building formula for cycle 1:
   vars 16 clauses 25
   Checking cycle 1:
   Checking secret 0 [17, 18]:
   Checking secret 1 [19, 20]:
   RST value:  1
   1
   Building formula for cycle 2:
   vars 21103 clauses 57104
   Checking cycle 2:
   Checking secret 0 [21427, 21104]:
   Checking secret 1 [21549, 21105]:
   RST value:  1
   1
   Building formula for cycle 3:
   vars 566836 clauses 1692708
   Checking cycle 3:
   Checking secret 0 [630522, 652105]:
   Finished in 34.31
   Writing a trace with the found error to [build_directory]/dbg-label-trace-0.txt
   Writing a reduced circuit to [build_directory]/tmp/dbg-circuit-0.dot
   The execution is not secure, here are some leaks:
   leak 0: (cycle: 3, cell: mux _10580_[0], id: 223382)
   3 stable  mux _10580_[0] vars   : ['s0:0', 's0:1']
   3 stable  mux _10580_[0] signals: u_otbn_core.u_otbn_rf_bignum.gen_rf_bignum_ff.u_otbn_rf_bignum_inner.rf[7800] ^ u_otbn_core.u_otbn_rf_bignum.gen_rf_bignum_ff.u_otbn_rf_bignum_inner.rf[7488]
   ```

## Individual steps in detail

Below we outline the individual steps performed by the `verify_otbn.sh` script.
This is useful if you, e.g., want to verify the masking of your own module.

For more details, please refer to the [Alma
tutorial](https://github.com/IAIK/coco-alma/tree/hw-verif#usage)

1. Make sure to source the `build_consts.sh` script from the OpenTitan
   repository in order to set up some shell variables.
   ```sh
   source ../opentitan/util/build_consts.sh
   ```

1. The first step involves the parsing of the synthesized netlist.
   ```sh
   python3 parse.py --keep --top-module otbn_top_coco --log-yosys \
      --source ${REPO_TOP}/hw/ip/otbn/pre_sca/alma/rtl/ram_1p.v \
      ${REPO_TOP}/hw/ip/otbn/pre_syn/syn_out/latest/generated/otbn_core.alma.v \
      ${REPO_TOP}/hw/ip/otbn/pre_sca/alma/rtl/otbn_top_coco.v
   ```

1. Next, run the `assemble.py` script to generate memory initialization file for
   OTBN.
   ```sh
   program=isw_and
   cd examples/otbn
   python3 assemble.py --program programs/${program}.S \
      --netlist ../../tmp/circuit.v
   cd ../../
   ```

1. Then, the Verilator testbench can be compiled and run. This step is required
   to identify control signals.
   ```sh
   python3 trace.py --testbench tmp/verilator_tb.c \
      --netlist tmp/circuit.v \
      --c-compiler gcc \
      --make-jobs 16
   ```
   Add `-b` argument to use cached object files from a previous Verilator run
   and save some time.

1. Next, the automatically generated labeling file `tmp/labels.txt` needs to be
   adapted. This file tells Alma which inputs of the DUT correspond to the
   secret shares and which ones are used to provide randomness for (re-)masking.
   It is pretty tedious to compute the actual indices for bignum register file
   labels. Generate it with the following command:
   ```sh
   examples/otbn/labels/generate_bignum_rf_labels.py \
      -i examples/otbn/labels/${program}_labels.txt \
      -o tmp/labels_updated.txt -w 1 -s 0
   ```

1. Finally the verification of the masking implementation can be started.
   ```sh
   python3 verify.py --json tmp/circuit.json \
      --top-module otbn_top_coco \
      --label tmp/labels_updated.txt \
      --vcd tmp/circuit.vcd \
      --checking-mode per-location \
      --rst-name rst_sys_n \
      --rst-phase 0 \
      --rst-cycles 2 \
      --init-delay 139 \
      --excluded-signals u_otbn_core.u_otbn_controller.rf_bignum_intg_err_i[0] \
      --dbg-signals otbn_cycle_cnt_o \
      --cycles 25 \
      --mode stable
   ```

Run the following command to see the waveform:
   ```sh
   gtkwave tmp/circuit.vcd
   ```

Run the following command to see the circuit diagramm if there is a leakage:
   ```sh
   xdot tmp/dbg-circuit-0.dot
   ```
