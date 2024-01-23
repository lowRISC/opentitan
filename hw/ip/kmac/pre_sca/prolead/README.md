# KMAC Masking Evaluation Using PROLEAD

This directory contains support files to evaluate the masking employed inside the SHA3 core of KMAC together with the instantiated PRNG using the tool [PROLEAD - A Probing-Based Leakage Detection Tool for Hardware and Software](https://github.com/ChairImpSec/PROLEAD).
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

   A netlist of the kmac_reduced module can be generated using the Yosys synthesis flow from the OpenTitan repository.
   From the OpenTitan top level, run
   ```sh
   cd hw/ip/kmac/pre_syn
   ```
   Set up the synthesis flow as described in the corresponding README.
   Then, make sure to change the line in `syn_setup.sh`
   ```sh
   export LR_SYNTH_TOP_MODULE=kmac
   ```
   to
   ```sh
   export LR_SYNTH_TOP_MODULE=kmac_reduced
   ```
   to only synthesize the masked SHA3 core and the PRNG without the TL-UL and key sideload interfaces, and related control logic.

   Then, run the synthesis
   ```sh
   ./syn_yosys.sh
   ```

## Evaluate the masking inside the SHA3 core together with the PRNG

After downloading and building the PROLEAD tool, and synthesizing the kmac_reduced module, the masking together with the PRNG can finally be evaluated.

1. Make sure to source the `build_consts.sh` script from the OpenTitan
   repository
   ```sh
   source util/build_consts.sh
   ```
   in order to set up some shell variables.

1. Enter the directory containing the PROLEAD support files for AES
   ```sh
   cd hw/ip/kmac/pre_sca/prolead
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
   Design file:    /scratch/vogelpi/ot/opentitan/hw/ip/kmac/pre_syn/syn_out/latest/generated/kmac_reduced_netlist.v
   Module name:    kmac_reduced
   Linker file:    linker.ld
   Settings file:  kmac_reduced_config.set
   Result folder:  out/kmac_reduced_2024_01_27_22_54_07

   Read library file...done!
   Read design file..."kmac_reduced"...done!
   Make circuit depth...done!
   Read settings file...done with 4 warnings!
       Warning "remove_full_probing_sets" is not specified. Default "remove_full_probing_sets" = no is taken!
       Warning "max_distance_multivariate" is not specified. Default "max_distance_multivariate" = 10 is taken!
       Warning "no_of_probing_sets_per_step" is not specified. Default "no_of_probing_sets_per_step" = all is taken!
       Warning "effect_size" is not specified. Default "effect_size" = 0.1 is taken!
   Construct probes...done!
   Prepare simulation memory...done!
   Prepare shared data for 16 threads ...done!

   Generate list of standard probes from 800 standard probe locations...96800 standard probes found...done!
   Generate list of extended probes from 1991 extended probe locations...1328701 extended probes found...done!
   Generate univariate probing sets...done (last step)! 96800 probing sets generated!
   Extend all probing sets...done!
   Remove duplicated probes in the sets...done!
   Remove duplicated probing sets...done! 96800 probing sets remain!
   ----------------------------------------------------------------------------------------------------------------------------------
   | #Standard Probes | #Extended Probes | Security Order | Distance | #Entries in Report | #Probing Sets | Maximum #Probes per Set |
   ----------------------------------------------------------------------------------------------------------------------------------
   |            96800 |           240911 |              1 |       10 |                 10 |         96800 |                      15 |
   ----------------------------------------------------------------------------------------------------------------------------------

   Evaluate security under the robust probing model!
   ---------------------------------------------------------------------------------------------------------------------------------
   |  Elapsed Time | Required Ram | Processed Simulations | ... Probing Set with highest Information Leakage | -log10(p) |  Status |
   ---------------------------------------------------------------------------------------------------------------------------------
   |   677.024361s |  46.084396GB |        128000 / 13275 | ..._chi_w[2].u_dom.u_prim_xor_t01.in1_i[54] (75) |  4.755748 |    OKAY |
   ---------------------------------------------------------------------------------------------------------------------------------
   |  1342.094709s |  46.084528GB |        256000 / 13275 | ...hi_w[3].u_dom.u_prim_xor_t01.in1_i[134] (132) |  4.951218 |    OKAY |
   ---------------------------------------------------------------------------------------------------------------------------------
   |  2051.522214s |  46.084528GB |        384000 / 13275 | ...chi_w[3].u_dom.u_prim_xor_t01.in1_i[36] (135) |  4.978313 |    OKAY |
   ---------------------------------------------------------------------------------------------------------------------------------
   |  2739.515661s |  46.084528GB |        512000 / 13275 | ..._chi_w[4].u_dom.u_prim_xor_t01.in1_i[74] (66) |  5.324674 | LEAKAGE |
   ---------------------------------------------------------------------------------------------------------------------------------
   |  3444.791637s |  46.084528GB |        640000 / 13275 | ..._chi_w[4].u_dom.u_prim_xor_t01.in1_i[27] (85) |  6.316023 | LEAKAGE |
   ---------------------------------------------------------------------------------------------------------------------------------
   |  4110.256030s |  46.084528GB |        768000 / 13275 | ...chi_w[3].u_dom.u_prim_xor_t01.in1_i[123] (90) |  6.112390 | LEAKAGE |
   ---------------------------------------------------------------------------------------------------------------------------------
   |  4813.111072s |  46.084528GB |        896000 / 13275 | ...chi_w[3].u_dom.u_prim_xor_t01.in1_i[123] (90) |  6.280869 | LEAKAGE |
   ---------------------------------------------------------------------------------------------------------------------------------
   |  5510.202187s |  46.084528GB |       1024000 / 13275 | ...chi_w[2].u_dom.u_prim_xor_t01.in1_i[38] (113) |  6.090532 | LEAKAGE |
   ---------------------------------------------------------------------------------------------------------------------------------
   ...
   ---------------------------------------------------------------------------------------------------------------------------------
   | 48528.091483s |  46.084528GB |       8960000 / 13275 | ...hi_w[2].u_dom.u_prim_xor_t01.in1_i[140] (118) |  4.767887 |    OKAY |
   ---------------------------------------------------------------------------------------------------------------------------------
   | 49310.377768s |  46.084528GB |       9088000 / 13275 | ...chi_w[1].u_dom.u_prim_xor_t01.in1_i[85] (135) |  4.629092 |    OKAY |
   ---------------------------------------------------------------------------------------------------------------------------------
   | 50232.143956s |  46.084528GB |       9216000 / 13275 | ...chi_w[1].u_dom.u_prim_xor_t01.in1_i[85] (135) |  5.019301 | LEAKAGE |
   ---------------------------------------------------------------------------------------------------------------------------------
   | 51160.724846s |  46.084528GB |       9344000 / 13275 | ...chi_w[1].u_dom.u_prim_xor_t01.in1_i[85] (135) |  5.170078 | LEAKAGE |
   ---------------------------------------------------------------------------------------------------------------------------------
   | 52075.464225s |  46.084528GB |       9472000 / 13275 | ...chi_w[1].u_dom.u_prim_xor_t01.in1_i[85] (135) |  4.846720 |    OKAY |
   ---------------------------------------------------------------------------------------------------------------------------------
   | 52891.872189s |  46.084528GB |       9600000 / 13275 | ...hi_w[2].u_dom.u_prim_xor_t01.in1_i[140] (118) |  5.170729 | LEAKAGE |
   ---------------------------------------------------------------------------------------------------------------------------------
   | 53595.527152s |  46.084528GB |       9728000 / 13275 | ...chi_w[1].u_dom.u_prim_xor_t01.in1_i[85] (135) |  5.240122 | LEAKAGE |
   ---------------------------------------------------------------------------------------------------------------------------------
   | 54282.137328s |  46.084528GB |       9856000 / 13275 | ...chi_w[1].u_dom.u_prim_xor_t01.in1_i[85] (135) |  5.804857 | LEAKAGE |
   ---------------------------------------------------------------------------------------------------------------------------------
   | 54950.055528s |  46.084528GB |       9984000 / 13275 | ...chi_w[1].u_dom.u_prim_xor_t01.in1_i[85] (135) |  6.094572 | LEAKAGE |
   ---------------------------------------------------------------------------------------------------------------------------------
   | 55633.918636s |  46.084528GB |      10112000 / 13275 | ...chi_w[1].u_dom.u_prim_xor_t01.in1_i[85] (135) |  5.299392 | LEAKAGE |
   ---------------------------------------------------------------------------------------------------------------------------------
   | 56336.821773s |  46.084528GB |      10240000 / 13275 | ...chi_w[4].u_dom.u_prim_xor_t01.in1_i[108] (87) |  5.221749 | LEAKAGE |
   ---------------------------------------------------------------------------------------------------------------------------------
   Evaluation done in 56337.2 seconds!
   done!
   ```
   It may be that PROLEAD reports several `-log10(p)` values greater than the threshold value of 5.0 and thus reports to have found leakage.
   However, as noted in the [PROLEAD wiki](https://github.com/ChairImpSec/PROLEAD/wiki/Results#interpretation), exceeding the 5.0 threshold is not a strict criterion for insecure designs.
   It's recommended to continue the evaluation and to consider the course of the `-log10(p)` values as the number of simulations increase.
   If the values do not grow in the further progression taking more simulations into account, the reported leakage probably occurred due to a false positive.
   It's further recommended to consider at least 10 or 100 Mio simulations for hardware designs when evaluating in the normal or compact mode, respectively.

   In this particular example, the evaluation is performed in normal mode and the `-log10(p)` values seem to oscillate around the threshold but they don't grow to infinity with 10 Mio simulations.
   The tool doesn't seem to provide a decisive result in this particular case.

## Adapting and creating new configuration files

When adapting and creating new configuration files it may be necessary to visually inspect wave dump files produced by PROLEAD to ensure the desired input values are applied with the correct timing.

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

- `kmac_reduced_config.set`: PROLEAD configuration file for evaluating the SHA3 core together with the PRNG.
- `library.lib`: Library file containing the information required for simulating the evaluated netlist.
                 The provided file contains a custom as well as the nangate45 library.
                 Edit this file to add support for additional standard cell libraries.
