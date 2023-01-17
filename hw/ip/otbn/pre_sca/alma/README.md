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
   `coco-otbn` branch of the tool
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
   Python environment
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
   required steps with a single command. Simply run
   ```sh
   ${REPO_TOP}/hw/ip/otbn/pre_sca/alma/verify_otbn.sh
   ```
   This should produce output similar to the one below:
   ```sh
   Verifying OTBN using Alma
   Starting yosys synthesis...
   | CircuitGraph | Total: 222852 | Linear: 22351 | Non-linear: 107350 | Registers: 17594 | Mux: 33864 |
   parse.py successful (732.40s)
   INSTR_LIMIT =  64
   Using program file:  programs/st_ok_tr_ok.S
   Using build directory: [build_directory]
   Using netlist path: ../../tmp/circuit.v
   Wrote verilator testbench to [build_directory]/verilator_tb.c
   It produces output VCD at [build_directory]/circuit.vcd
   1: Running verilator on given netlist
   2: Compiling verilated netlist library
   3: Compiling provided verilator testbench
   4: Simulating circuit and generating VCD
   | CircuitGraph | Total: 222852 | Linear: 22351 | Non-linear: 107350 | Registers: 17594 | Mux: 33864 |
   tmp/circuit.vcd:53125: [WARNING] Entry for name clk_sys already exists in namemap (clk_sys -> }c2)
   tmp/circuit.vcd:53144: [WARNING] Entry for name imem_wdata_i already exists in namemap (imem_wdata_i -> ~c2)
   tmp/circuit.vcd:53145: [WARNING] Entry for name imem_we_i already exists in namemap (imem_we_i -> \"d2)
   tmp/circuit.vcd:53146: [WARNING] Entry for name imem_wmask_i already exists in namemap (imem_wmask_i -> #d2)
   tmp/circuit.vcd:53150: [WARNING] Entry for name rst_sys_n already exists in namemap (rst_sys_n -> %d2)
   RST value:  1
   1
   Building formula for cycle 0:
   vars 0 clauses 0
   Checking cycle 0:
   Checking secret 0 [1, 2]:
   RST value:  1
   1
   Building formula for cycle 1:
   vars 7 clauses 9
   Checking cycle 1:
   Checking secret 0 [8, 9]:
   RST value:  1
   1
   Building formula for cycle 2:
   vars 14 clauses 18
   Checking cycle 2:
   Checking secret 0 [15, 16]:
   ...
   RST value:  1
   1
   Building formula for cycle 173:
   vars 1211 clauses 1557
   Checking cycle 173:
   Checking secret 0 [1212, 1213]:
   RST value:  1
   1
   Building formula for cycle 174:
   vars 1218 clauses 1566
   Checking cycle 174:
   Checking secret 0 [1219, 1220]:
   Finished in 65.81
   The execution is secure
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
   program=st_ok_tr_ok
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
   secret shares and which ones are used to provide randomness for
   (re-)masking. Update the labels file or use an existing one.

1. Finally the verification of the masking implementation can be started.
   ```sh
   python3 verify.py --json tmp/circuit.json \
      --top-module otbn_top_coco \
      --label examples/otbn/labels/${program}_labels.txt \
      --vcd tmp/circuit.vcd \
      --mode stable \
      --rst-name rst_sys_n \
      --rst-phase 0 \
      --rst-cycles 2 \
      --cycles 175 \
      --from-cycle 140
   ```

Run the following command to see the waveform:
   ```sh
   gtkwave tmp/circuit.vcd
   ```
