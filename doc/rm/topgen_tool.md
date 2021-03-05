---
title: "Top Generation Tool"
---

The top generation tool `topgen.py` is used to build top specific modules for a specific OpenTitan design - for example [`top_earlgrey`](https://github.com/lowRISC/opentitan/tree/master/hw/top_earlgrey).
Currently, as part of this generation process, the following top specific modules are created
* Overall top module
* Platform level interrupt controller
* Pinmux
* Crossbar

This document explains the overall generation process, the required inputs, the output locations, as well as how the tool should be invoked.

## Generation Process

### Overview
The details of a particular OpenTitan variant is described in a top specific Hjson file.
For example see [`top_earlgrey`](https://github.com/lowRISC/opentitan/tree/master/hw/top_earlgrey/data/top_earlgrey.hjson).

The top specific Hjson describes how the design looks and how it should connect, for example:
* Overall fabric data width
* Clock sources
* Reset sources
* List of instantiated peripherals
  * Module type of each peripheral (it is possible to have multiple instantitations of a particular module)
  * Clock / reset connectivity of each peripheral
  * Base address of each peripheral
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

The topgen tool thus hierarchically gathers and generates the missing information from additional Hjson files that describe the detail of each component.
These are primarily located in two places:
* `hw/ip/data/*.hjson`
* `hw/top_*/data/xbar_*.hjson`

In the process of gathering, each individual Hjson file is validated for input correctness and then merged into a final generated Hjson output that represents the complete information that makes up each OpenTitan design.
For example, see [`top_earlgrey`](https://github.com/lowRISC/opentitan/tree/master/hw/top_earlgrey/data/autogen/top_earlgrey.gen.hjson).
Note specifically the generated interrupt list, the pinmux connections, and the port-to-net mapping of clocks and resets, all of which were not present in the original input.

The purpose for this two step process, instead of describing the design completely inside one Hjson file, is to decouple the top and components development while allowing re-use of components by multiple tops.

This process also clearly separates what information needs to be known by top vs what needs to be known by a specific component.
For example, a component does not need to know how many clock sources a top has or how many muxed pins it contains.
Likewise, the top does not need to know the details of why an interrupt is generated, just how many there are.
The user supplied `top_*.hjson` thus acts like a integration specification while the remaining details are filled in through lower level inputs.

In addition to design collateral, the tool also generates all the top level RAL (Register Abstraction Layer) models necessary for verification.

### Validation, Merge and Output

As stated previously, each of the gathered component Hjson files is validated for correctness.
For the peripherals, this is done by invoking `util/reggen/validate.py`, while the  xbar components are validated through `util/tlgen/validate.py`.
The peripheral and xbar components are then validated through `topgen/validate.py`, which checks for interrupt, pinmux, clock and reset consistency.

Once all validation is passed, the final Hjson is created.
This Hjson is then used to generate the final top rtl in the top-specific [autogen directory](https://github.com/lowRISC/opentitan/tree/master/hw/top_earlgrey/rtl/autogen).
The other top specific modules are generated in the top ip-specific autogen directories, for example [plic](https://github.com/lowRISC/opentitan/tree/master/hw/top_earlgrey/ip/rv_plic), [xbar](https://github.com/lowRISC/opentitan/tree/master/hw/top_earlgrey/ip/xbar) and [pinmux](https://github.com/lowRISC/opentitan/tree/master/hw/top_earlgrey/ip/pinmux).

As part of this process, topgen invokes other tools, please see the documentation for [`reggen`](register_tool.md) and [`tlgen`](crossbar_tool.md) for more tool specific details.

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
  --no-plic             If defined, topgen doesn't generate the interrup controller RTLs.
  --no-gen-hjson        If defined, the tool assumes topcfg as a generated hjson. So it
                        bypasses the validation step and doesn't read ip and xbar
                        configurations
  --top-only            If defined, the tool generates top RTL only
  --xbar-only           If defined, the tool generates crossbar RTLs only
  --plic-only           If defined, the tool generates RV_PLIC RTL and Hjson only
  --hjson-only          If defined, the tool generates complete Hjson only
  --top_ral, -r         If set, the tool generates top level RAL model for DV

```
