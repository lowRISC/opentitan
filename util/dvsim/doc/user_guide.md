---
title: "DVSim user guide"
---

# Prerequisites

Please ensure that the chosen EDA tool's binary path is added to the `$PATH` variable, and any shared libraries that need to be visible to other associated tools are added to the `$LD_LIBRARY_PATH` variable.

Please refer to the tool vendor documentation to ensure that these settings have been applied before invoking DVSim.
DVSim also does not currently enforce that a particular tool version is used.
It is upto the project stakeholders to collectively decide and agree upon a specific tool version ([example](https://github.com/lowRISC/opentitan/issues/16617)).
A more robust mechanism to ensure the right tool versions are in use could be set up in future.

# Cannonical examples

## Simulations

## Lint

## FPV

## Synthesis

## CDC

## RDC

# Output directory structure

## Job status indicators

# General options

## `--help`

This argument provides a quick reference on how to invoke the tool, with various supported options.

```console
$ ./util/dvsim/dvsim.py --help
usage: dvsim.py <cfg-hjson-file> [-h] [options]

dvsim is a command line tool to deploy ASIC tool flows such as
regressions for design verification (DV), formal property verification
(FPV), linting and synthesis.

It uses hjson as the format for specifying what to build and run. It
is an end-to-end regression manager that can deploy multiple builds
(where some tests might need different set of compile time options
requiring a uniquely build sim executable) in parallel followed by
tests in parallel using the load balancer of your choice.

dvsim is built to be tool-agnostic so that you can easily switch
between the tools at your disposal. dvsim uses fusesoc as the starting
step to resolve all inter-package dependencies and provide us with a
filelist that will be consumed by the sim tool.

positional arguments:
  <cfg-hjson-file>      Configuration hjson file.

options:
  -h, --help            show this help message and exit
  --version             Print version and exit
  --tool TOOL, -t TOOL  Explicitly set the tool to use. This is optional for running simulations (where it can be set in an .hjson file), but is required for other flows. Possible tools include: vcs, questa,xcelium, ascentlint, verixcdc, mrdc, veriblelint,verilator, dc.
  --list [CAT ...], -l [CAT ...]
                        Parse the the given .hjson config file, list the things that can be run, then exit. The list can be filtered with a space-separated of categories from: build_modes, run_modes, tests, regressions.

Choosing what to run:
  -i [ITEMS ...], --items [ITEMS ...]
                        Specify the regressions or tests to run. Defaults to "smoke", but can be a space separated list of test or regression names.
  --select-cfgs [CFG ...]
                        The .hjson file is a primary config. Only run the given configs from it. If this argument is not used, dvsim will process all configs listed in a primary config.

Dispatch options:
  --job-prefix PFX      Prepend this string when running each tool command.
  --local               Force jobs to be dispatched locally onto user's machine.
  --remote              Trigger copying of the repo to scratch area.
  --max-parallel N, -mp N
                        Run only up to N builds/tests at a time. Default value 16, unless the DVSIM_MAX_PARALLEL environment variable is set, in which case that is used. Only applicable when launching jobs locally.
  --gui                 Run the flow in interactive mode instead of the batch mode.

File management:
  --scratch-root PATH, -sr PATH
                        Destination for build / run directories. If not specified, uses the path in the SCRATCH_ROOT environment variable, if set, or ./scratch otherwise.
  --proj-root PATH, -pr PATH
                        The root directory of the project. If not specified, dvsim will search for a git repository containing the current directory.
  --branch B, -br B     By default, dvsim creates files below {scratch-root}/{dut}.{flow}.{tool}/{branch}. If --branch is not specified, dvsim assumes the current directory is a git repository and uses the name of the current branch.
  --max-odirs N, -mo N  When tests are run, older runs are backed up. Discard all but the N most recent (defaults to 5).
  --purge               Clean the scratch directory before running.

Options for building:
  --build-only, -bu     Stop after building executables for the given items.
  --build-unique        Append a timestamp to the directory in which files are built. This is suitable for the case when another test is already running and you want to run something else from a different terminal without affecting it.
  --build-opts OPT [OPT ...], -bo OPT [OPT ...]
                        Additional options passed on the command line each time a build tool is run.
  --build-modes MODE [MODE ...], -bm MODE [MODE ...]
                        The options for each build_mode in this list are applied to all build and run targets.
  --build-timeout-mins BUILD_TIMEOUT_MINS
                        Wall-clock timeout for builds in minutes: if the build takes longer it will be killed.

Options for running:
  --run-only, -ru       Skip the build step (assume that simulation executables have already been built).
  --run-opts OPT [OPT ...], -ro OPT [OPT ...]
                        Additional options passed on the command line each time a test is run.
  --run-modes MODE [MODE ...], -rm MODE [MODE ...]
                        The options for each run_mode in this list are applied to each simulation run.
  --profile [P], -p [P]
                        Turn on simulation profiling (where P is time or mem).
  --xprop-off           Turn off X-propagation in simulation.
  --no-rerun            Disable the default behaviour, where failing tests are automatically rerun with waves enabled.
  --run-timeout-mins RUN_TIMEOUT_MINS
                        Wall-clock timeout for runs in minutes: if the run takes longer it will be killed.
  --verbosity V, -v V   Set tool/simulation verbosity to none (n), low (l), medium (m), high (h), full (f) or debug (d). The default value is set in config files.

Build / test seeds:
  --build-seed [S]      Randomize the build. Uses the seed value passed an additional argument, else it randomly picks a 32-bit unsigned integer.
  --seeds S [S ...], -s S [S ...]
                        A list of seeds for tests. Note that these specific seeds are applied to items being run in the order they are passed.
  --fixed-seed S        Run all items with the seed S. This implies --reseed 1.
  --reseed N, -r N      Override any reseed value in the test configuration and run each test N times, with a new seed each time.
  --reseed-multiplier N, -rx N
                        Scale each reseed value in the test configuration by N. This allows e.g. running the tests 10 times as much as normal while maintaining the ratio of numbers of runs between different tests.

Dumping waves:
  --waves {fsdb,shm,vpd,vcd,evcd,fst}, -w {fsdb,shm,vpd,vcd,evcd,fst}
                        Enable dumping of waves. It takes an argument to pick the desired wave format.By default, dumping waves is not enabled.
  --max-waves N, -mw N  Only dump waves for the first N tests run. This includes both tests scheduled for run and those that are automatically rerun.

Generating simulation coverage:
  --cov, -c             Enable collection of coverage data.
  --cov-merge-previous  Only applicable with --cov. Merge any previous coverage database directory with the new coverage database.
  --cov-unr             Run coverage UNR analysis and generate report. This only supports VCS now.
  --cov-analyze         Rather than building or running any tests, analyze the coverage from the last run.

Generating and publishing results:
  --map-full-testplan   Show complete testplan annotated results at the end.
  --publish             Publish results to reports.opentitan.org.

Controlling DVSim itself:
  --print-interval N, -pi N
                        Print status every N seconds.
  --verbose [D]         With no argument, print verbose dvsim tool messages. With --verbose=debug, the volume of messages is even higher.
  --dry-run, -n         Print dvsim tool messages but don't actually run any command

Either place the positional argument ahead of the optional args:
eg. `dvsim.py <cfg-hjson-file> -i ITEM ITEM`
or end a sequence of optional args with `--`:
eg. `dvsim.py -i ITEM ITEM -- <cfg-hjson-file>`
```


# Options for simulations

## `--seeds`

## `--reseed`

### Specifying build options

### Specifying build modes

### Dumping waves

### Enabling coverage

# Options for FPV

# Options for lint

# Options for synthesis

# Options for CDC

# Options for RDC
