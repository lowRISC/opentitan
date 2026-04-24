# OTBN Masking Leakage Analysis Using PROLEAD

This directory contains support files to perform leakage analysis on OTBN gadget implementations using [PROLEAD](https://github.com/ChairImpSec/PROLEAD), a probing-based leakage detection tool.

## Prerequisites

1. Clone the PROLEAD repository and check out the tested commit.
   ```sh
   git clone https://github.com/ChairImpSec/PROLEAD.git
   cd PROLEAD
   git checkout 5a433b10
   ```

1. Build the tool inside its Nix development shell.
   ```sh
   nix-shell
   make release
   ```

1. If `nix-shell` fails to find packages, update the Nix channel metadata first.
   ```sh
   nix-channel --update
   ```
   Then re-run `nix-shell` and `make release`.

1. Generate a gate-level netlist for the gadget under test using the synthesis flow from the OpenTitan repository.
   From the OpenTitan top level, run
   ```sh
   cd hw/ip/otbn/pre_syn
   ```
   Set up the synthesis flow as described in the README in the pre_syn folder, then run
   ```sh
   ./syn_yosys_sec_add.sh <gadget>
   ```

## Running the leakage analysis

After building PROLEAD and synthesizing the target gadget:

1. Source the `build_consts.sh` script from the OpenTitan repository to set up the required shell variables.
   ```sh
   source ../opentitan/util/build_consts.sh
   ```

1. Change to this directory.
   ```sh
   cd ../opentitan/hw/ip/otbn/pre_sca/prolead
   ```

1. Launch the analysis script, passing the name of the gadget to evaluate.
   ```sh
   ./evaluate.sh <gadget>
   ```
   Supported gadgets are: `hpc2`, `hpc2o`, `hpc3`, `hpc3o`.
   The default (no argument) runs the full `mask_accelerator` wrapper.

   Results are written to `out/<gadget>_<timestamp>/` and a symlink `out/latest` points to the most recent run.
