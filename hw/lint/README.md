# RTL Linting

Linting is a productivity tool for designers to quickly find typos and
bugs at the time when the RTL is written. Running lint is important
when using SystemVerilog, a weakly-typed language, unlike other hardware
description languages. We consider linting to be critical for conformance
to our goals of high quality designs.

We have chosen [Ascent
Lint](https://www.realintent.com/rtl-linting-ascent-lint/) by Real Intent
as our linter of choice for hardware design collateral.
In the current state of the project, the lint policy file and waiver
files are **not** checked into the repo, but are being kept
privately. The lint scripts in this repo don't need a policy file and
waiver files, you can still run lint without them.

See below instructions on how lint is executed on a design. The goal
is zero Errors for each design either through code fixing
(preferred) or lint waivers (where justified).

## Setup

1.  Install the latest fusesoc version needed for lint:

        cd <the-root-directory-which-contains-the-hw-directory>
        pip3 install -U -r python-requirements.txt --user

1.  Install and load ascentlint: version
    `2018.A.p10G.2020_07_31` of ascentlint is being used.
    In case you use `module load`, make sure to load the correct version.

## Running Lint

**Example 1**: To run lint on module `gpio.sv`, type:

    cd hw/lint
    lint gpio

Above generates the lint report file `lint.rpt`, which details all lint errors
and warning.

**Example 2**: You can also run lint on any submodule of the design, not
  just the ones that have a `.core` file. For example, to run lint on submodule
  `gpio_reg_top.sv`, tye:

    cd hw/lint
    lint gpio_reg_top

## Running Lint on the Entire Design

To run lint on all blocks and the toplevel, type:

    cd hw/lint
    lint_all | tee lint_all.std

The script `lint_all` can be used for continuous integration.
