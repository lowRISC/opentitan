# OTBN Masking Leakage Analysis Using PROLEAD

This directory contains support files to perform leakage analysis on OTBN gadget implementations using [PROLEAD](https://github.com/ChairImpSec/PROLEAD), a probing-based leakage detection tool.


## Prerequisites

1. Clone the PROLEAD repository and check out the tested commit.
   ```sh
   git clone https://github.com/ChairImpSec/PROLEAD.git
   cd PROLEAD
   git checkout 5a433b10
   ```

1. If you are using nix-shell as your development environment, set it up as following:
   Build the tool inside its Nix development shell.
   ```sh
   nix-shell
   make release
   ```
   If you would like to set up PROLEAD differently, please refer to the README in the PROLEAD repository.

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
   Supported gadgets are: `hpc2`, `hpc2o`, `hpc3`, `hpc3o`.


## Running the leakage analysis

After building PROLEAD and synthesizing the target gadget:

1. Source the `build_consts.sh` script from the OpenTitan repository to set up the required shell variables.
   ```sh
   source ${REPO_TOP}/util/build_consts.sh
   ```

1. Change to this directory.
   ```sh
   cd ${REPO_TOP}/hw/ip/otbn/pre_sca/prolead
   ```

1. Launch the analysis script, passing the name of the gadget to evaluate.
   ```sh
   ./evaluate.sh <gadget>
   ```
   The default (no argument) runs the full `mask_accelerator` wrapper.

   Results are written to `out/<gadget>_<timestamp>/` and a symlink `out/latest` points to the most recent run.

   A successful run produces output similar to the following (shown for `hpc2`):

   ```
   [2026-04-30 12:26:28] Successfully validated the settings file.
   [2026-04-30 12:26:28] Successfully read the library with name "nang45".
   [2026-04-30 12:26:28] Successfully parsed 35 cells from the library.
   [2026-04-30 12:26:28] Successfully read design file with topmodule "prim_hpc2_sca_wrapper"!
   [2026-04-30 12:26:28] Successfully matched 1 fresh mask signals (for rising edge) [{rand_i}].
   [2026-04-30 12:26:28] Successfully detected 372 possible probes in total.
   [2026-04-30 12:26:28] Successfully initialized a univariate evaluation with 125 probing sets.
   [2026-04-30 12:26:28] -------------------------------------------------------------------------------------------------------------------------------------
   [2026-04-30 12:26:28] | #Standard Probes | #Extended Probes | #Probing Sets | Minimum #Probes per Set | Maximum #Probes per Set | Average #Probes per Set |
   [2026-04-30 12:26:28] -------------------------------------------------------------------------------------------------------------------------------------
   [2026-04-30 12:26:28] |              125 |              192 |           125 |                       2 |                       8 |                4.400000 |
   [2026-04-30 12:26:28] -------------------------------------------------------------------------------------------------------------------------------------
   [2026-04-30 12:26:28] -----------------------------------------------------------------------------------------------------------------------------------
   [2026-04-30 12:26:28] | Elapsed Time |        Used Memory |          #Simulations | Probing Set with Highest Information Leakage |  -log10(p) |  Status |
   [2026-04-30 12:26:28] -----------------------------------------------------------------------------------------------------------------------------------
   [2026-04-30 12:26:29] |   0-00:00:01 |   0TB    0GB 104MB |         128000 / 9629 |                                      _20_(4) |   2.076636 |    OKAY |
   ...
   [2026-04-30 12:26:42] |   0-00:00:14 |   0TB    0GB 104MB |        1536000 / 9629 |                                      _10_(5) |   1.238617 |    OKAY |
   ```

   The `-log10(p)` column shows the statistical significance of the highest leakage observed.
   A value consistently below 5 across all simulations indicates no detectable leakage.
