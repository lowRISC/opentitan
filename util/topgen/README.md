# Top Generation Tool

The top generation tool `topgen.py` is used to build top specific modules for a specific OpenTitan design - for example [`top_earlgrey`](https://github.com/lowRISC/opentitan/tree/master/hw/top_earlgrey).
Currently, as part of this generation process, the following top specific modules are created
* Overall top module
* Crossbars
* A number of templated peripherals, which are expanded according to top specific configurations
This document explains the overall generation process, the required inputs, the output locations, as well as how the tool should be invoked.

## Generation Process

### Overview
The details of a particular OpenTitan variant is described in a top specific Hjson file.
For example see [`top_earlgrey`](https://github.com/lowRISC/opentitan/tree/master/hw/top_earlgrey/data/top_earlgrey.hjson).

The top specific Hjson describes how the design looks and how it should connect, for example:
* Overall fabric data width
* Clock sources
* Reset sources
* Address spaces
* List of instantiated peripherals
  * Module type of each peripheral (it is possible to have multiple instantiations of a particular module)
  * Clock / reset connectivity of each peripheral
  * Base address of each peripheral for each connected address space
* System memories
* Fabric construction
  * Clock / reset connectivity of each fabric component
* Interrupt sources
* Pinmux construction
  * List of dedicated or muxed pins

The top level Hjson however, does not contain details such as:
* Specific clock / reset port names for each peripheral
* Number of interrupts in each peripheral
* Number of input or output pins in each peripheral
* Details of crossbar connection and which host can reach which device

There are two kinds of peripherals:
* Generic peripherals, which are the same for any top configuration
* Ipgen peripherals, which have a set of template files, and are expanded based on top-specific parameters

The topgen tool thus hierarchically gathers and generates the missing information from additional Hjson files that describe the detail of each component.
These are primarily located in the following places:
* `hw/ip/*/data/*.hjson` for generic peripherals
* `hw/ip_templates/*/data/*.hjson.tpl` for ipgen peripherals
* `hw/top_*/data/xbar_*.hjson` for crossbars which are also generated from templates

In the process of gathering, each individual Hjson file is validated for input correctness and then merged into a final generated Hjson output that represents the complete information that makes up each OpenTitan design.
For example, see [`top_earlgrey`](https://github.com/lowRISC/opentitan/tree/master/hw/top_earlgrey/data/autogen/top_earlgrey.gen.hjson).
Note specifically the generated interrupt list, the pinmux connections, and the port-to-net mapping of clocks and resets, all of which were not present in the original input.

The purpose for this two step process, instead of describing the design completely inside one Hjson file, is to decouple the top and components development while allowing re-use of components by multiple tops.

This process also clearly separates what information needs to be known by top vs. what needs to be known by a specific component.
For example, a component does not need to know how many clock sources a top has or how many muxed pins it contains.
Likewise, the top does not need to know the details of why an interrupt is generated, just how many there are.
The user supplied `top_*.hjson` thus acts like a integration specification while the remaining details are filled in through lower level inputs.

In addition to design collateral, the tool also generates all the top level RAL (Register Abstraction Layer) models necessary for verification.

### Validation, Merge and Output

As stated previously, each of the gathered component Hjson files is validated for correctness.
For the peripherals, this is done by invoking `util/reggen/validate.py`, while the  xbar components are validated through `util/tlgen/validate.py`.
The peripheral and xbar components are then validated through `util/topgen/validate.py`.
This performs extensive checks on the top configuration, for example interrupt, pinmux, clock and reset consistency.

Once all validation is passed, the final Hjson is created by `util/topgen/merge.py`.
This Hjson is then used to generate the final top RTL.

As part of this process, topgen invokes other tools.
Please see the documentation for [`ipgen`](../ipgen/README.md), [`reggen`](../reggen/README.md), and [`tlgen`](../tlgen/README.md) for more tool specific details.

### Generation Flow

In order to generate the complete set of artifacts for a given top the first step is to generate the complete top configuration file (named `top_*/data/autogen/top_*.gen.hjson` as mentioned above).
Most other artifacts, like the top-level module(s), ipgen peripherals, and top-level SV and software collateral require this file for generation.
These artifacts can be generated independently and concurrently from the complete top configuration.

#### Generating the Complete Top Configuration

The generation of ipgen peripherals is delicate since they depend on each other.
All these dependencies are captured in the top configuration as it is completed.
As ipgen peripherals are expanded they provide information that will be used for expanding other ipgen peripherals.
This means the order in which ipgen peripherals are expanded needs to be carefully chosen in order to avoid multiple generation passes.
The top configuration is completed progressively as individual peripherals are processed.
All this is done in-memory, and the individual peripherals are added in the following order:
* The generic peripherals
* The ipgen peripherals, topologically sorted based on their inter-dependencies
* The crossbars

It is important to progressively complete the top config with the most up-to-date data specific to each ipgen peripheral before expanding it.
The completion is done using functions that are called in merge_top, except they get an extra argument to allow incomplete configuration since not all ipgen peripherals will have been expanded.
Once all ipgen peripherals are expanded one last merge is performed, this time not allowing incomplete configurations.
To make sure there are no mistakes in the order of ipgen peripherals the expansion can make multiple generation passes, stopping when the complete top configuration is stable.

#### Generating other Artifacts

There is a large number of artifacts that are generated from the complete top config using topgen, including:
* The templates of ipgen peripherals are expanded into directories specific to each top, for example `hw/top_darjeeling/ip_autogen/clkmgr`.
* The crossbars are also expanded from templates into top-specific directories, for example `hw/top_earlgrey/ip/xbar_*/*/autogen`.
* Part of the Bazel files necessary to register the top with build system, see [Creating a new top](../../hw/top/doc/create_top.md) for details.

## Usage

The most generic use of topgen is to let it generate everything.
This can be done through direct invocation, or the `${REPO_TOP}/hw` makefile.
The example below shows the latter:
```console
$ cd ${REPO_TOP}
$ make -C hw top
```

It is possible to restrict what the tool should generate.

```console
$ cd ${REPO_TOP}
$ ./util/topgen.py -h
usage: topgen [-h] --topcfg TOPCFG [--outdir OUTDIR] [--verbose] [--no-top]
              [--no-xbar] [--no-plic] [--no-gen-hjson] [--top-only] [--xbar-only]
              [--plic-only] [--hjson-only] [--top_ral]

optional arguments:
  -h, --help            show this help message and exit
  --topcfg TOPCFG, -t TOPCFG
                        `top_{name}.hjson` file.
  --outdir OUTDIR, -o OUTDIR
                        Target TOP directory. Module is created under rtl/. (default:
                        dir(topcfg)/..)
  --verbose, -v         Verbose
  --no-top              If defined, topgen doesn't generate top_{name} RTLs.
  --no-xbar             If defined, topgen doesn't generate crossbar RTLs.
  --no-plic             If defined, topgen doesn't generate the interrupt controller RTLs.
  --no-gen-hjson        If defined, the tool assumes topcfg as a generated hjson. So it
                        bypasses the validation step and doesn't read ip and xbar
                        configurations
  --top-only            If defined, the tool generates top RTL only
  --xbar-only           If defined, the tool generates crossbar RTLs only
  --plic-only           If defined, the tool generates RV_PLIC RTL and Hjson only
  --hjson-only          If defined, the tool generates complete Hjson only
  --top_ral, -r         If set, the tool generates top level RAL model for DV

```

## Random Netlist Constants Generation for Tapeout

Topgen uses a cryptographically secure random number generator (CSRNG) for generating random netlist constants such as hardware PRNG reset values and output permutations, default SRAM scrambling keys used after reset, ROM scrambling keys, lifecycle controller unlock tokens and diversification constants, and OTP scrambling keys.
The algorithm used by topgen is CTR_DRBG as standardized in [NIST SP 800-90A](https://csrc.nist.gov/pubs/sp/800/90/a/r1/final) with a key length of 256 bits.
The CTR_DRBG algorithm guarantees both forward and backward secrecy, i.e., outputs cannot be computed from any previous or future outputs, as well as enhanced backward secrecy, meaning outputs cannot be computed from a compromised internal state.
For more details, please check the NIST SP 800-90A standard as well as the implementation used by topgen (see [secure_prng.py](https://github.com/lowRISC/opentitan/blob/master/util/topgen/secure_prng.py)).

For testing and open source development purposes, OpenTitan provides a set of testing seeds for the different CTR_DRBG instances used by topgen as well as constants.
These are used by default and they can be found here:
- [`hw/top_*/data/top_*_seed.testing.hjson`](https://github.com/lowRISC/opentitan/blob/master/hw/top_earlgrey/data/top_earlgrey_seed.testing.hjson) contains actual 256-bit seeds for three CTR_DRBG instances: one for generating random netlist constants, one for generating OTP images, and one for generating the lifecycle controller unlock tokens.
- [`hw/top_*/rtl/autogen/testing/lc_ctrl_token_pkg.sv`](https://github.com/lowRISC/opentitan/blob/master/hw/top_earlgrey/rtl/autogen/testing/lc_ctrl_token_pkg.sv) contains the randomly generated lifecycle controller unlock tokens.
- [`hw/top_*/rtl/autogen/testing/top_*_rnd_const_pkg.sv`](https://github.com/lowRISC/opentitan/blob/master/hw/top_earlgrey/rtl/autogen/testing/top_earlgrey_rnd_cnst_pkg.sv) contains the randomly generated netlist constants such hardware PRNG reset values and permutations etc.

When moving to tapeout, it is important to re-seed each of the different CTR_DRBG instances used by topgen with a dedicated 256-bit seed produced from a secure source of high-quality randomness such as a hardware security module (HSM) to profit from the security guarantees mentioned above.
These seeds, together with the constants generated by topgen, as well as the actual netlist must then be treated as secret, i.e., they must not leave the tapeout environment and they must not be pushed back into the open source repository.

To clearly separate testing and tapeout seeds and constants, the following steps should be used (for simplicity, the process is exemplified for the Earl Grey top level but it works very similarly for other top levels):

1. Copy the file `hw/top_earlgrey/data/top_earlgrey_seed.testing.hjson` and rename it to `hw/top_earlgrey/data/top_earlgrey_seed.tapeout.hjson`.
   You only have to do this for the specific top level you want to tape out.

1. Open the file `hw/top_earlgrey/data/top_earlgrey_seed.tapeout.hjson` and replace the three different seed values with custom 256-bit seeds extracted from a secure source of high-quality randomness such as an HSM.

1. Type `make -C hw all TOPS=top_earlgrey SEED_MODE=tapeout`.
   This will generate the following new files:
   - `hw/top_earlgrey/data/autogen/top_earlgrey.secrets.tapeout.gen.hjson`
   - `hw/top_earlgrey/rtl/autogen/tapeout/`
     - `lc_ctrl_token_pkg.sv`
     - `top_earlgrey_rnd_cnst_pkg.sv`
     - `top_earlgrey_rnd_cnst_pkg.vbl`
     - `top_earlgrey_tapeout_lc_ctrl_token_pkg.core`
     - `top_earlgrey_tapeout_rnd_cnst_pkg.core`

To use these tapeout files instead of the testing files, you have to
instruct the involved tools accordingly.

### Synthesis

For synthesis, the `fileset_tapeout` flag has to be provided to  FuseSoC to use these tapeout files instead of the testing files.

Execute
```
fusesoc --cores-root . run --target=syn --tool icarus --flag fileset_tapeout --no-export --setup lowrisc:systems:chip_earlgrey_asic
```
to prepare the filelist for synthesis.

To check that the correct tapeout files are used, you can inspect the generated filelist inside `build/lowrisc_systems_chip_earlgrey_asic_0.1/syn-icarus/lowrisc_systems_chip_earlgrey_asic_0.1.scr`.

### Chip-Level Tests

To run a chip-level test using these tapeout files, the following steps are required.

1. Open the `hw/top_earlgrey/dv/chip_sim_cfg.hjson` file and extend the `overrides` section as follows:
   ```
   // Override existing project defaults to supply chip-specific values.
   overrides: [
     ...
     // FuseSoC SystemVerilog filelist generation flags
     {
       name : sv_flist_gen_flags
       value : ["--flag=fileset_tapeout"]
     }
     ...
   ]
   ```
1. In the same file (`chip_sim_cfg.hjson`), extend the `sw_build_opts` entry as follows:
   ```
   // Add default software build options.
   sw_build_opts: [
     "--//hw/top:seed=tapeout",
   ]
   ```
   In case the entry does not yet exist, add it directly after the `sw_build_device` entry.

1. In the same file (`chip_sim_cfg.hjson`), modify the `gen_otp_top_secret_cfg` entry as follows:
   ```
   gen_otp_top_secret_cfg: "{proj_root}/hw/{top_chip}/data/autogen/{top_chip}.secrets.tapeout.gen.hjson"
   ```

1. Open the `hw/top_earlgrey/defs.bzl` file and extend the `secret_cfgs` entry as follows:
   ```
   secret_cfgs = {
     "testing": "//hw/top_earlgrey/data/autogen:top_earlgrey.secrets.testing.gen.hjson",
     "tapeout": "//hw/top_earlgrey/data/autogen:top_earlgrey.secrets.tapeout.gen.hjson",
    },
   ```

You can then type the usual command, e.g.,
```
./util/dvsim/dvsim.py hw/top_earlgrey/dv/chip_sim_cfg.hjson -i chip_sw_uart_tx_rx
```
to start the chip-level test.

To check that the correct tapeout files are used, you can inspect the exported sources under `scratch/master/chip_earlgrey_asic-sim-vcs/default/fusesoc-work/src/lowrisc_earlgrey_constants_*`.

To be on the safe side and prevent the accidental use of testing files for the tapeout, it is recommended to delete the following testing files and directories:
  - `hw/top_earlgrey/data/autogen/top_earlgrey.secrets.testing.gen.hjson`
  - `hw/top_earlgrey/rtl/autogen/testing/*`

Note that the `hw/top_earlgrey/data/top_earlgrey_seed.testing.hjson` file is still required by the `ralgen` generator (but the actual seed values don't matter for `ralgen`).
