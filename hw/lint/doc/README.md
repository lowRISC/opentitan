---
title: "Linting"
---

# RTL Linting

Linting is a productivity tool for designers to quickly find typos and bugs at the time when the RTL is written.
Running lint is important when using SystemVerilog, a weakly-typed language, unlike other hardware description languages.
We consider linting to be critical for conformance to our goals of high quality designs.

We have standardized on the [AscentLint](https://www.realintent.com/rtl-linting-ascent-lint/) tool from RealIntent for this task due to its fast run-times and comprehensive set of rules that provide concise error and warning messages.

The lint flow leverages a new lint rule policy named _"lowRISC Lint Rules"_ that has been tailored towards our [Verilog Style Guide](https://github.com/lowRISC/style-guides/blob/master/VerilogCodingStyle.md).
The lint flow run scripts and waiver files are available in the GitHub repository of this project, but due to the proprietary nature of the lint rules and their configuration, the _"lowRISC Lint Rules"_ lint policy file can not be publicly provided.
However, the _"lowRISC Lint Rules"_ are available as part of the default policies in AscentLint release 2019.A.p3 or newer (as `LRLR-v1.0.policy`).
This enables designers that have access to this tool to run the lint flow provided locally on their premises.

Our linting flow leverages FuseSoC to resolve dependencies, build file lists and call the linting tools. See [here](https://github.com/olofk/fusesoc) for an introduction to this opensource package manager and [here](https://docs.opentitan.org/doc/ug/install_instructions/) for installation instructions.

In order to run lint on a [comportable IP](https://docs.opentitan.org/doc/rm/comportability_specification/) block, the corresponding FuseSoC core file must have a lint target and include (optional) waiver files as shown in the following example taken from the FuseSoC core of the AES comportable IP:
```
filesets:

  [...]

  files_verilator_waiver:
    depend:
      # common waivers
      - lowrisc:lint:common
      - lowrisc:lint:comportable
    files:
      - lint/aes.vlt
    file_type: vlt

  files_ascentlint_waiver:
    depend:
      # common waivers
      - lowrisc:lint:common
      - lowrisc:lint:comportable
    files:
      - lint/aes.waiver
    file_type: waiver

  files_veriblelint_waiver:
    depend:
      # common waivers
      - lowrisc:lint:common
      - lowrisc:lint:comportable
  [...]

targets:
  default: &default_target
    filesets:
      - tool_verilator   ? (files_verilator_waiver)
      - tool_ascentlint  ? (files_ascentlint_waiver)
      - tool_veriblelint ? (files_veriblelint_waiver)
      - files_rtl
    toplevel: aes

  lint:
    <<: *default_target
    default_tool: verilator
    parameters:
      - SYNTHESIS=true
    tools:
      ascentlint:
        ascentlint_options:
          - "-wait_license"
          - "-stop_on_error"
      verilator:
        mode: lint-only
        verilator_options:
          - "-Wall"
```
Note that the setup shown above also supports RTL style linting with the open source tool [Verible](https://github.com/google/verible/) and RTL linting with [Verilator](https://www.veripool.org/wiki/verilator) in order to complement the sign-off lint flow with AscentLint.
In particular, Verible lint focuses on different aspects of the code, and detects style elements that are in violation with our [Verilog Style Guide](https://github.com/lowRISC/style-guides/blob/master/VerilogCodingStyle.md).

The same lint target is reused for all three tools (we override the tool selection when invoking FuseSoC).
Lint waivers can be added to the flow by placing them in the corresponding waiver file.
In this example this would be `lint/aes.waiver` for AscentLint and `lint/aes.vlt` for Verilator.

All three linting tools mentioned above have been integrated with the `dvsim` regression tool.
In order to manually invoke any of the linting tools on a specific block, make sure that the corresponding linting tool is properly installed, step into the project root and call
```console
$ cd $REPO_TOP
$ util/dvsim/dvsim.py hw/top_earlgrey/lint/top_earlgrey_lint_cfgs.hjson --tool (ascentlint|verilator|veriblelint) --purge --select-cfgs <lint-config-name>
```
where `<lint-config-name>` is the name of the linting configuration as defined in the `top_earlgrey_lint_cfgs.hjson` regression list (currently that file contains a lint configuration for all available comportable IPs and the top-level).

In order to run all defined configs in `top_earlgrey_lint_cfgs.hjson` as a batch regression, just omit the `--select-cfgs` switch as follows:
```console
$ cd $REPO_TOP
$ util/dvsim/dvsim.py hw/top_earlgrey/lint/top_earlgrey_lint_cfgs.hjson --tool (ascentlint|verilator|veriblelint) --purge
```
The `purge` option ensures that the scratch directory is fully erased before starting the build.
Depending on the number of AscentLint licenses that can be checked out at a time, you may also want to set the number of parallel workers to one using `--max-parallel <number>`.

Batch regressions for all three tools are regularly run on the `master` branch at eight-hour intervals, and the results are published on a public dashboard such that everybody can inspect the current lint status of all IPs on the project website.
The dashboard can be found by following the appropriate link on the [hardware IP overview page](https://docs.opentitan.org/hw).

# CDC Linting

Logic designs that have signals that cross from one clock domain to
another unrelated clock domain are notorious for introducing hard to
debug problems.  The reason is that design verification, with its constant
and idealized timing relationships on signals, does not represent the
variability and uncertainty of real world systems.  For this reason,
maintaining a robust Clock Domain Crossing verification strategy ("CDC
methodology") is critical to the success of any multi-clock design.

Currently, due to the proprietary nature of tool collateral, all CDC linting
activity is done offline and reported back to designers.  The project will
standardize on a particular CDC linting tool, and results will be shared in
some form through continuous integration build results, published tool
outputs, pre-submit checks, and/or linting summaries of tool output
(TODO: publication details).  At that time this README will be updated
with setup and run instructions.

This holds for *Reset Domain Crossing* ("RDC") methodology as well.
