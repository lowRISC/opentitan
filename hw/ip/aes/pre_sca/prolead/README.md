# AES Masking Evaluation Using PROLEAD

This directory contains support files to evaluate the masking employed inside the AES cipher core together with the instantiated PRNG using the tool [PROLEAD - A Probing-Based Leakage Detection Tool for Hardware and Software](https://github.com/ChairImpSec/PROLEAD).
For further details on the tool and its capabilities, refer to the paper [PROLEAD - A Probing-Based Hardware Leakage Detection Tool](https://eprint.iacr.org/2022/965).

## Prerequisites

Note that this flow is experimental.
It has been developed using Yosys 0.36 (git sha1 8f07a0d84) and sv2v v0.0.11-28-g81d8225.
The used PROLEAD version is from Oct 31, 2023 (7ed0f9f2).
Other versions of these tools might not be compatible.

1. Download the PROLEAD tool
   ```sh
   git clone git@github.com:ChairImpSec/PROLEAD.git
   cd PROLEAD
   git reset --hard 7ed0f9f2
   ```

   Install the PROLEAD requirements as documented in the [corresponding wiki page](https://github.com/ChairImpSec/PROLEAD/wiki/Installation#installation).

   In the PROLEAD directory, run
   ```sh
   make release -j 16
   ```
   to build the tool.

   The compiled binary can be found in the `release` directory.
   Make sure to add it to your path.

1. Generate a Verilog netlist

   A netlist of the AES cipher core can be generated using the Yosys synthesis flow from the OpenTitan repository.
   From the OpenTitan top level, run
   ```sh
   cd hw/ip/aes/pre_syn
   ```
   Set up the synthesis flow as described in the corresponding README.
   Then, make sure to change the line in `syn_setup.sh`
   ```sh
   export LR_SYNTH_TOP_MODULE=aes
   ```
   to
   ```sh
   export LR_SYNTH_TOP_MODULE=aes_cipher_core
   ```
   to only synthesize the masked AES cipher core without the TL-UL and key sideload interfaces, unmasked datapath logic for the different block cipher modes of operation, and related control logic.

   Then, run the synthesis
   ```sh
   ./syn_yosys.sh
   ```

## Evaluate the masking inside the AES cipher core together with the PRNG

After downloading and building the PROLEAD tool, and synthesizing the AES cipher core, the masking together with the PRNG can finally be evaluated.

1. Make sure to source the `build_consts.sh` script from the OpenTitan
   repository
   ```sh
   source util/build_consts.sh
   ```
   in order to set up some shell variables.

1. Enter the directory containing the PROLEAD support files for AES
   ```sh
   cd hw/ip/aes/pre_sca/prolead
   ```

1. Launch the PROLEAD tool to evaluate the netlist using the provided script
   ```sh
   ./evaluate.sh
   ```
   This should produce output similar to the one below:
   ```sh
   Start Hardware Leakage Evaluation

   Library file:   library.lib
   Library name:   NANG45
   Design file:    opentitan/hw/ip/aes/pre_syn/syn_out/latest/generated/aes_cipher_core_netlist.v
   Module name:    aes_cipher_core
   Linker file:    linker.ld
   Settings file:  aes_cipher_core_config.set
   Result folder:  out/latest

   Read library file...done!
   Read design file..."aes_cipher_core"...done!
   Make circuit depth...done!
   Read settings file...done with 4 warnings!
       Warning "remove_full_probing_sets" is not specified. Default "remove_full_probing_sets" = no is taken!
       Warning "max_distance_multivariate" is not specified. Default "max_distance_multivariate" = 10 is taken!
       Warning "no_of_probing_sets_per_step" is not specified. Default "no_of_probing_sets_per_step" = all is taken!
       Warning "effect_size" is not specified. Default "effect_size" = 0.1 is taken!
   Construct probes...done!
   Prepare simulation memory...done!
   Prepare shared data for 16 threads ...done!

   Generate list of standard probes from 224 standard probe locations...12992 standard probes found...done!
   Generate list of extended probes from 786 extended probe locations...943370 extended probes found...done!
   Generate univariate probing sets...done (last step)! 12992 probing sets generated!
   Extend all probing sets...done!
   Remove duplicated probes in the sets...done!
   Remove duplicated probing sets...done! 12992 probing sets remain!
   ----------------------------------------------------------------------------------------------------------------------------------
   | #Standard Probes | #Extended Probes | Security Order | Distance | #Entries in Report | #Probing Sets | Maximum #Probes per Set |
   ----------------------------------------------------------------------------------------------------------------------------------
   |            12992 |            45588 |              1 |       10 |                 10 |         12992 |                     127 |
   ----------------------------------------------------------------------------------------------------------------------------------

   Evaluate security under the robust probing model!
   -------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------
   | Elapsed Time | Required Ram | Processed Simulations |                                                                      Probing Set with highest Information Leakage | -log10(p) |  Status |
   -------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------
   |  112.107951s |  12.510552GB |       128000 / 161575 | ...gen_sbox_i[2].u_aes_sbox_ij.gen_sbox_masked.gen_sbox_dom.u_aes_sbox.u_aes_dom_inverse_gf2p8.b_y10_prd1[2] (37) |  3.620547 |    OKAY |
   -------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------
   |  235.358985s |  12.510552GB |       256000 / 161585 | \u_aes_sub_bytes.gen_sbox_j[3].gen_sbox_i[2].u_aes_sbox_ij.gen_sbox_masked.gen_sbox_dom.u_aes_sbox.prd1_d[6] (17) |  5.025905 | LEAKAGE |
   -------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------
   |  358.192534s |  12.510552GB |       384000 / 161585 | \u_aes_sub_bytes.gen_sbox_j[2].gen_sbox_i[3].u_aes_sbox_ij.gen_sbox_masked.gen_sbox_dom.u_aes_sbox.prd1_d[0] (12) |  3.363567 |    OKAY |
   -------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------
   |  473.133173s |  12.510552GB |       512000 / 161585 | ...gen_sbox_i[2].u_aes_sbox_ij.gen_sbox_masked.gen_sbox_dom.u_aes_sbox.u_aes_dom_inverse_gf2p8.b_y10_prd1[2] (37) |  3.921945 |    OKAY |
   -------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------
   |  590.334307s |  12.510552GB |       640000 / 161585 | \u_aes_sub_bytes.gen_sbox_j[3].gen_sbox_i[2].u_aes_sbox_ij.gen_sbox_masked.gen_sbox_dom.u_aes_sbox.prd1_d[1] (12) |  4.717441 |    OKAY |
   -------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------
   |  706.490746s |  12.510552GB |       768000 / 161585 | \u_aes_sub_bytes.gen_sbox_j[0].gen_sbox_i[0].u_aes_sbox_ij.gen_sbox_masked.gen_sbox_dom.u_aes_sbox.prd1_d[2] (57) |  3.492387 |    OKAY |
   -------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------
   |  895.176681s |  12.510552GB |       896000 / 161585 |   ...gen_sbox_masked.gen_sbox_dom.u_aes_sbox.u_aes_dom_inverse_gf2p8.u_aes_dom_inverse_gf2p4.b_gamma_ss_d[1] (22) |  3.981567 |    OKAY |
   -------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------
   | 1030.569630s |  12.510552GB |      1024000 / 161585 | \u_aes_sub_bytes.gen_sbox_j[0].gen_sbox_i[3].u_aes_sbox_ij.gen_sbox_masked.gen_sbox_dom.u_aes_sbox.prd1_d[6] (62) |  3.393895 |    OKAY |
   -------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------
   ...
   -------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------
   | 8518.762592s |  12.510552GB |      9088000 / 161585 | \u_aes_sub_bytes.gen_sbox_j[0].gen_sbox_i[2].u_aes_sbox_ij.gen_sbox_masked.gen_sbox_dom.u_aes_sbox.prd1_d[2] (41) |  3.017296 |    OKAY |
   -------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------
   | 8639.829626s |  12.510552GB |      9216000 / 161585 | \u_aes_sub_bytes.gen_sbox_j[2].gen_sbox_i[3].u_aes_sbox_ij.gen_sbox_masked.gen_sbox_dom.u_aes_sbox.prd1_d[6] (41) |  3.018391 |    OKAY |
   -------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------
   | 8758.906474s |  12.510552GB |      9344000 / 161585 | \u_aes_sub_bytes.gen_sbox_j[3].gen_sbox_i[3].u_aes_sbox_ij.gen_sbox_masked.gen_sbox_dom.u_aes_sbox.prd1_d[5] (42) |  2.945251 |    OKAY |
   -------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------
   | 8881.120705s |  12.510552GB |      9472000 / 161585 | \u_aes_sub_bytes.gen_sbox_j[3].gen_sbox_i[0].u_aes_sbox_ij.gen_sbox_masked.gen_sbox_dom.u_aes_sbox.prd1_d[4] (46) |  2.996482 |    OKAY |
   -------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------
   | 8998.628485s |  12.510552GB |      9600000 / 161585 | \u_aes_sub_bytes.gen_sbox_j[3].gen_sbox_i[2].u_aes_sbox_ij.gen_sbox_masked.gen_sbox_dom.u_aes_sbox.prd1_d[7] (51) |  2.976931 |    OKAY |
   -------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------
   | 9111.867212s |  12.510552GB |      9728000 / 161585 | ...gen_sbox_i[1].u_aes_sbox_ij.gen_sbox_masked.gen_sbox_dom.u_aes_sbox.u_aes_dom_inverse_gf2p8.b_y10_prd1[1] (57) |  3.198678 |    OKAY |
   -------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------
   | 9223.720210s |  12.510552GB |      9856000 / 161585 | ...gen_sbox_i[1].u_aes_sbox_ij.gen_sbox_masked.gen_sbox_dom.u_aes_sbox.u_aes_dom_inverse_gf2p8.b_y10_prd1[1] (57) |  3.256948 |    OKAY |
   -------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------
   | 9343.188344s |  12.510552GB |      9984000 / 161585 | ...gen_sbox_i[1].u_aes_sbox_ij.gen_sbox_masked.gen_sbox_dom.u_aes_sbox.u_aes_dom_inverse_gf2p8.b_y10_prd1[1] (57) |  3.390740 |    OKAY |
   -------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------
   | 9458.458347s |  12.510552GB |     10112000 / 161585 | ...gen_sbox_i[1].u_aes_sbox_ij.gen_sbox_masked.gen_sbox_dom.u_aes_sbox.u_aes_dom_inverse_gf2p8.b_y10_prd1[1] (57) |  3.097989 |    OKAY |
   -------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------
   | 9572.974702s |  12.510552GB |     10240000 / 161585 | ...gen_sbox_i[1].u_aes_sbox_ij.gen_sbox_masked.gen_sbox_dom.u_aes_sbox.u_aes_dom_inverse_gf2p8.b_y10_prd1[1] (57) |  3.264392 |    OKAY |
   -------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------
   Evaluation done in 9573.98 seconds!
   done!
   ```
   It may be that PROLEAD reports several `-log10(p)` values greater than the threshold value of 5.0 and thus reports to have found leakage.
   However, as noted in the [PROLEAD wiki](https://github.com/ChairImpSec/PROLEAD/wiki/Results#interpretation), exceeding the 5.0 threshold is not a strict criterion for insecure designs.
   It's recommended to continue the evaluation and to consider the course of the `-log10(p)` values as the number of simulations increase.
   If the values do not grow in the further progression taking more simulations into account, the reported leakage probably occurred due to a false positive.
   It's further recommended to consider at least 10 or 100 Mio simulations for hardware designs when evaluating in the normal or compact mode, respectively.

   In this particular example, the evaluation is performed in normal mode and all `-log10(p)` values for more than 384sk simulations are below the threshold.
   It can thus be assumed that the values above the threshold are false positives.

   By default, the script will evaluate the AES cipher core including the PRNG.
   But you can actually specify the top module to evaluate.
   For example, to verify a single AES S-Box, first re-run the Yosys synthesis with
   ```sh
   export LR_SYNTH_TOP_MODULE=aes_sbox
   ```
   and then execute
   ```sh
   ./evaluate.sh aes_sbox
   ```
   Note that you need to create a dedicated PROLEAD config file for this.

## Adapting and creating new configuration files

When adapting and creating new configuration files, e.g., to evaluate the masked AES S-Box in isolation, it may be necessary to visually inspect wave dump files produced by PROLEAD to ensure the desired input values are applied with the correct timing.

To this end, it's advisable to temporarily change the configuration as follows:
```
% total number of simulations (traces) in the tests, should be a factor of 64
no_of_simulations
64

% number of simulations in each step, should be a factor of 64, and a divisor of no_of_simulations
no_of_step_simulations
64

% number of simulations in each step that result files are written, should be a factor of 64, and
% a divisor of no_of_simulations and should be a factor of no_of_step_simulations
no_of_step_write_results
64

waveform_simulation % yes/no: whether VCD files of individual simulations are stored to disk (in
                    % main directory) or not, can be useful for debugging the configuration
yes
```

You can then run the evaluation using `evaluate.sh`.
The waves are stored in per-simulation value change dump (VCD) files in the current directory.

The VCDs can be opened using e.g. GTKWave.
Based on this, you can tune the section of the configuration file applying the inputs during the initial clock cycles.
This section typically starts with something like:
```
% number of clock cycles to initiate the run (start of encryption)
no_of_initial_clock_cycles
11
```

In addition, also the following settings found at the end of the configuration file may need to be changed:
- `end_condition`
- `end_wait_cycles`
- `max_clock_cycle`
- `no_of_outputs`
- `no_of_test_clock_cycles`
- `probes_exclude`
- `probes_include`

For details regarding these settings, check out the comments in the provided configuration file as well as the [PROLEAD wiki](https://github.com/ChairImpSec/PROLEAD/wiki).

After finishing the tuning of the settings, don't forget to set the `waveform_simulation` setting back to `no`.
Otherwise, PROLEAD might try to fill your disk with millions of VCDs.

## Details of the provided support files

- `aes_cipher_core_config.set`: PROLEAD configuration file for evaluating the AES cipher core including the PRNG.
- `library.lib`: Library file containing the information required for simulating the evaluated netlist.
                 The provided file contains a custom as well as the nangate45 library.
                 Edit this file to add support for additional standard cell libraries.
