# AES Formal Masking Verification Using Alma

This directory contains support files to formally verify the masking employed
inside AES unit using the tool [Alma:
Execution-aware Masking Verification](https://github.com/IAIK/coco-alma).

## Prerequisites

Note that this flow is experimental. It has been developed using Yosys 0.9+4306
(git sha1 3931b3a03) and sv2v v0.0.9-24-gf868f06. Other tool versions might not
be compatible.

1. Download the Alma tool

   Note that since we are primarily interested in verifying the masking of a
   hardware implementation, we are using the `hw-verif` branch of the tool. In
   addition, we currently need to use a patched version of the tool, to work
   around a limitation.
   ```sh
   git clone git@github.com:vogelpi/coco-alma.git alma -b fix-yosys-synth-template
   ```
   The tip of this branch should be c8c7f67.

   Enter the directory using
   ```sh
   cd alma
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

1. Generate a Verilog netlist

   A netlist of the DUT can be generated using the Yosys synthesis flow from
   the OpenTitan repository. From the OpenTitan top level, run
   ```sh
   cd hw/ip/aes/pre_syn
   ```
   Set up the synthesis flow as described in the corresponding README. Then,
   make sure to change the line in `syn_setup.sh`
   ```sh
   export LR_SYNTH_TOP_MODULE=aes
   ```
   to
   ```sh
   export LR_SYNTH_TOP_MODULE=aes_sbox
   ```
   to only synthesize an individual AES S-Box as formally verifying the entire
   AES unit or the AES cipher core is currently out of scope from a tool run
   time point of view. Alternatively, it is possible to verify `aes_sub_bytes`
   containing all 16 S-Boxes of the data path or even `aes_reduced_round` which
   besides the S-Boxes also includes the ShiftRows and MixColumns operations.

   Then run the synthesis
   ```sh
   ./syn_yosys.sh
   ```

## Formally verifying the masking of the AES unit

After downloading the Alma tool, installing dependencies and synthesizing AES,
the masking can finally be formally verified.

1. Make sure to source the `build_consts.sh` script from the OpenTitan
   repository
   ```sh
   source util/build_consts.sh
   ```
   in order to set up some shell variables.

1. Enter the directory where you have downloaded Alma and load the virtual
   Python environment
   ```sh
   source dev/bin/activate
   ```

1. Launch the Alma tool to parse, trace (simulate) and formally verify the
   netlist. For simplicity, a single script is provided to launch all the
   required steps with a single command. Simply run
   ```sh
   ${REPO_TOP}/hw/ip/aes/pre_sca/alma/verify_aes.sh
   ```
   This should produce output similar to the one below:
   ```sh
   Verifying aes_sbox using Alma
   File tmp/circuit.v already exists, do you want to overwrite it? (y/n)  y
   Starting yosys synthesis...
   | CircuitGraph | Total: 1692 | Linear:  504 | Non-linear:  375 | Registers:  167 | Mux:  228 |
   parse.py successful (2.80s)
   1: Running verilator on given netlist
   2: Compiling verilated netlist library
   3: Compiling provided verilator testbench
   4: Simulating circuit and generating VCD
   | CircuitGraph | Total: 1692 | Linear:  504 | Non-linear:  375 | Registers:  167 | Mux:  228 |
   tmp/tmp.vcd:1286: [WARNING] Entry for name clk_i already exists in namemap (clk_i -> K,)
   tmp/tmp.vcd:1287: [WARNING] Entry for name data_i already exists in namemap (data_i -> L,)
   tmp/tmp.vcd:1288: [WARNING] Entry for name data_o already exists in namemap (data_o -> M,)
   tmp/tmp.vcd:1289: [WARNING] Entry for name en_i already exists in namemap (en_i -> N,)
   tmp/tmp.vcd:1381: [WARNING] Entry for name mask_i already exists in namemap (mask_i -> O,)
   tmp/tmp.vcd:1382: [WARNING] Entry for name mask_o already exists in namemap (mask_o -> P,)
   tmp/tmp.vcd:1383: [WARNING] Entry for name op_i already exists in namemap (op_i -> Q,)
   tmp/tmp.vcd:1384: [WARNING] Entry for name out_ack_i already exists in namemap (out_ack_i -> R,)
   tmp/tmp.vcd:1385: [WARNING] Entry for name out_req_o already exists in namemap (out_req_o -> S,)
   tmp/tmp.vcd:1386: [WARNING] Entry for name prd_i already exists in namemap (prd_i -> T,)
   tmp/tmp.vcd:1387: [WARNING] Entry for name rst_ni already exists in namemap (rst_ni -> U,)
   0
   0
   Building formula for cycle 0: vars 0 clauses 0
   Checking cycle 0:
   Building formula for cycle 1: vars 114 clauses 312
   Checking cycle 1:
   Building formula for cycle 2: vars 3276 clauses 10534
   Checking cycle 2:
   Checking probe (cycle 2, and _0436_[0]): 0.00
   Checking probe (cycle 2, and _0378_[0]): 0.00
   ...
   Checking probe (cycle 5, not gen_sbox_masked.gen_sbox_dom.u_aes_sbox.u_aes_dom_inverse_gf2p8.u_aes_dom_inverse_gf2p4.u_aes_dom_mul_gamma1_gamma0.u_prim_xilinx_buf_mul_abx_z0.out_o[2]): 0.00
   Checking probe (cycle 5, xor gen_sbox_masked.gen_sbox_dom.u_aes_sbox.u_aes_dom_inverse_gf2p8.u_aes_dom_inverse_gf2p4.u_aes_dom_mul_gamma1_gamma0.u_prim_xilinx_buf_mul_abx_z0.out_o[3]): 0.00
   Checking probe (cycle 5, mux _0914_[0]): 0.00
   Checking probe (cycle 5, mux _0912_[0]): 0.00
   Checking probe (cycle 5, mux _0925_[0]): 0.00
   Checking probe (cycle 5, mux _0923_[0]): 0.00
   Checking probe (cycle 5, mux _0945_[0]): 0.00
   Checking probe (cycle 5, mux _0943_[0]): 0.00
   Checking probe (cycle 5, mux _0898_[0]): 0.00
   Checking probe (cycle 5, mux _0913_[0]): 0.00
   Checking probe (cycle 5, mux _0911_[0]): 0.00
   Checking probe (cycle 5, mux _0897_[0]): 0.00
   Finished in 50.74
   The execution is secure
   ```
   By default, this script will verify the AES S-Box. But you can actually
   specify the top module to verify. For example, to verify a single, reduced
   AES round without AddKey operation, first re-run the Yosys synthesis with
   ```sh
   export LR_SYNTH_TOP_MODULE=aes_reduced_round
   ```
   and then execute
   ```sh
   ${REPO_TOP}/hw/ip/aes/pre_sca/alma/verify_aes.sh aes_reduced_round
   ```

## Individual steps in detail

Below we outline the individual steps performed by the `verify_aes.sh` script.
This is useful if you, e.g., want to verify the masking of your own module.
For this how to, we focus on the most simple case, i.e., the formal
verification of a single AES S-Box.

For more details, please refer to the [Alma tutorial](https://github.com/IAIK/coco-alma/tree/hw-verif#usage).

1. The first step involves the parsing the synthesized netlist.
   ```sh
   ./parse.py --top-module aes_sbox \
      --source ${REPO_TOP}/hw/ip/aes/pre_syn/syn_out/latest/generated/aes_sbox.alma.v \
      --netlist tmp/circuit.v --log-yosys
   ```

1. Next, the automatically generated labeling file `tmp/labels.txt` needs to be
   adapted. This file tells Alma which inputs of the DUT correspond to the
   secret shares and which ones are used to provide randomness for
   (re-)masking. Open the file and change the lines
   ```
   data_i [7:0] = unimportant
   mask_i [7:0] = unimportant
   prd_i [27:0] = unimportant
   ```
   to
   ```
   data_i [7:0] = secret 7:0
   mask_i [7:0] = secret 7:0
   prd_i [27:0] = random
   ```

1. Then the Verilator testbench can be compiled and run required to identify
   control signals and the like
   ```sh
   ./trace.py --testbench ${REPO_TOP}/hw/ip/aes/pre_sca/alma/cpp/verilator_tb_aes_sbox.cpp \
     --netlist tmp/circuit.v -o tmp/circuit
   ```

1. Finally the verification of the masking implementation can be started.

   ```sh
   ./verify.py --json tmp/circuit.json \
     --label tmp/labels.txt \
     --top-module aes_sbox \
     --vcd tmp/tmp.vcd \
     --rst-name rst_ni --rst-phase 0 \
     --probe-duration once \
     --mode transient \
     --glitch-behavior loose \
     --cycles 6
   ```

## Details of the provided support files

- `cpp`: SystemVerilog testbench, instantiates and drives the synthesized
  netlist of the DUT.
- `verify_aes.sh`: Script to run the parse, trace and compile steps with
  one single command.
