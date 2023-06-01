# Building (and Testing) Software

_Before following this guide, make sure you have read the_:
* main [Getting Started](README.md) instructions,
* install Verilator section of the [Verilator guide](./setup_verilator.md), and
* [OpenTitan Software](https://opentitan.org/book/sw/) documentation.

All OpenTitan software is built with [Bazel](https://bazel.build/).
Additionally, _most_ tests may be run with Bazel too.

## TL;DR
To install the correct version of bazel, build, and run a single test with Verilator, run:

```console
$REPO_TOP/bazelisk.sh test --test_output=streamed --disk_cache=~/bazel_cache //sw/device/tests:uart_smoketest_sim_verilator
```

This will take a while (an hour on a laptop is typical) if it's your first build or the first after a `git pull`, because Bazel has to build the chip simulation.
Future builds will be much faster; go get a coffee and come back later.

If the test worked, your OpenTitan setup is functional; you can build the software and run on-device tests using the Verilator simulation tool.
See [Running Tests with Bazel](#running-tests with Bazel) for information on how to find and run other tests.

If the test didn't work, read the full guide, especially the [Troubleshooting](#troubleshooting) section.

## Installing Bazel

There are two ways to install the correct version of Bazel:
1. **automatically**, using the `bazelisk.sh` script provided in the repo, or
1. **manually**.

### Automatic Installation

To simplify the installation of Bazel, and provide a means to seamlessly update the Bazel version we use in the future, we provide a shell script that acts as a wrapper for invocations of "`bazel ...`".
To use it, you have two options:
1. use "`./bazelisk.sh ...`" instead of "`bazel ...`" to invoke of Bazel subcommands, or
1. set the following alias (e.g., in your `.bashrc` file) to accomplish the same:
```console
alias bazel="$REPO_TOP/bazelisk.sh"
```

### Manual Installation

This section is optional and can be skipped if you completed the instructions above in _Automatic Installation_.

While the automatic installation is convenient, by installing Bazel directly, you can get some quality of life features like tab completion.
If you haven't yet installed Bazel, and would like to, you can add it to apt and install it on Ubuntu systems with the following commands [as described in the Bazel documentation](https://bazel.build/install/ubuntu):

```console
sudo apt install apt-transport-https curl gnupg
curl -fsSL https://bazel.build/bazel-release.pub.gpg | gpg --dearmor > bazel.gpg
sudo mv bazel.gpg /etc/apt/trusted.gpg.d/
echo "deb [arch=amd64] https://storage.googleapis.com/bazel-apt stable jdk1.8" |
sudo tee /etc/apt/sources.list.d/bazel.list
sudo apt update && sudo apt install bazel-5.1.1
sudo ln -s /usr/bin/bazel-5.1.1 /usr/bin/bazel
```

or by following [instructions for your system](https://bazel.build/install).

## Building Software with Bazel

Running
```console
bazel build //sw/...
```
will build all software in our repository.
If you do not have Verilator installed yet, you can use the `--define DISABLE_VERILATOR_BUILD=true` flag to skip the jobs that depend on that.

In general, you can build any software target (and all of it's dependencies) using the following syntax:
```console
bazel build @<repository>//<package>:<target>
```
Since most targets are within the main Bazel repository (`lowrisc_opentitan`), you can often drop the "`@<repository>`" prefix.
For example, to build the boot ROM we use for testing (also referred to as the _test ROM_), you can use
```console
bazel build //sw/device/lib/testing/test_rom:test_rom
```
Additionally, some Bazel syntactic sugar enables dropping the target name when the target name matches the last subcomponent of the package name.
For example, the following is equivalent to the above
```console
bazel build //sw/device/lib/testing/test_rom
```

For more information on Bazel repositories, packages, and targets, please refer to the Bazel [documentation](https://bazel.build/concepts/build-ref).

## Running Tests with Bazel

In addition to building software, Bazel is also used to build and run tests.
There are two categories of OpenTitan tests Bazel can build and run:
1. on-host, and
1. on-device.

On-host tests are compiled and run on the host machine, while on-device tests are compiled and run on (simulated/emulated) OpenTitan hardware.

Examples of on-host tests are:
* unit tests for device software, such as [DIF](https://opentitan.org/book/sw/device/lib/dif/) and [ROM](https://opentitan.org/book/sw/device/silicon_creator/rom/) unit tests.
* any test for host software, such as `opentitan{lib,tool}`.

Examples of on-device tests are:
* [chip-level tests](https://opentitan.org/book/sw/device/tests/).
* [ROM functional tests](https://opentitan.org/book/sw/device/silicon_creator/rom/)

Test target names normally match file names (for instance, `//sw/device/tests:uart_smoketest` corresponds to `sw/device/test/uart_smoketest.c`).
You can see all tests available under a given directory using `bazel query`, e.g.:

```console
bazel query 'tests(//sw/device/tests/...)'
```
### Tags and wildcards

TLDR: `bazelisk.sh test --test_tag_filters=-cw310,-verilator,-vivado,-jtag,-eternal,-broken --build_tag_filters=-vivado,-verilator //...`
*Should* be able to run all the tests and build steps in OpenTitan that don't require optional setup steps, and

You may find it useful to use wildcards to build/test all targets in the OpenTitan repository instead of individual targets.
`//sw/...` is shorthand for all targets in `sw` that isn't tagged with manual.
If a target (a test or build artifact) relies on optional parts of the "Getting Started" guide they should be tagged so they can be filtered out and users can `bazelisk.sh test //...` once they filter out the appropriate tags.
We maintain or use the following tags to support this:
* `broken` is used to tag tests that are committed but should not be expected by CI or others to pass.
* `cw310`, `cw310_test_rom`, and `cw310_rom` are used to tag tests that depend on a correctly setup cw310 "Bergen Board" to emulate OpenTitan.
  The `cw310` tag may be used in `--test_tag_filters` to enable concise filtering to select tests that run on this board and include or exclude them.
  Loading the bitstream is the slowest part of the test, so these tags can group tests with common bitstreams to accelerate the tests tagged `cw310_test_rom`.
* `verilator` is used to tag tests that depend on a verilated model of OpenTitan that can take a significant time to build.
  Verilated tests can still be built with `--define DISABLE_VERILATOR_BUILD`, but they will skip the invocation of Verilator and cannot be run.
* `vivado` is used to tag tests that critically depend on Vivado.
* `jtag` is used to tag tests that rely on a USB JTAG adapter connected like we have in CI.
* `manual` is a Bazel builtin that prevents targets from matching wildcards.
  Test suites are typically tagged manual so their contents match, but test suites don't get built or run unless they're intentionally invoked.
  Intermediate build artifacts may also be tagged with manual to prevent them from being unintentionally built if they cause other problems.
* `skip_in_ci` is used to tag ROM end-to-end tests that we currently skip in CI.
  ROM end-to-end tests are typically written for five life cycle states: TEST\_UNLOCKED0, DEV, PROD, PROD\_END, and RMA.
  This tag allows us to limit the tests run in CI to a single life cycle state, allowing CW310 tests to finish in a reasonable timeframe.
  We run tests for the remaining lifecycle states outside the CI in a less frequent manner.

`ci/scripts/check-bazel-tags.sh` performs some useful queries to ensure these tags are applied.
These tags can then be used to filter tests using `--build_tests_only --test_tag_filters=-cw310,-verilator,-vivado`.
These tags can also be used to filter builds using `--build_tag_filters=-cw310,-verilator,-vivado`.

`--build_tests_only` is important when matching wildcards if you aren't using
`--build_tag_filters` to prevent `bazelisk.sh test //...` from building targets that are filtered out by `--test_tag_filters`.

There is no way to filter out dependencies of a test\_suite such as `//sw/device/tests:uart_smoketest` (Which is a suite that's assembled by the `opentitan_functest` rule) from a build.

### Running on-device Tests

On-device tests such as `//sw/device/tests:uart_smoketest` include multiple targets for different device simulation/emulation tools.
Typically, you will only want to run one of these test targets at a time (for instance, only Verilator or only FPGA).
Add `_sim_verilator` to the test name to run the test on Verilator only, and `_fpga_cw310_rom` or `_fpga_cw310_test_rom` to run the test on FPGA only.

You can check which Verilator tests are available under a given directory using:
```console
bazel query 'attr(tags, verilator, tests(//sw/device/tests/...))'
```

For FPGA tests, just change the tag:
```console
bazel query 'attr(tags, cw310, tests(//sw/device/tests/...))'
```

For more information, please refer to the [Verilator](./setup_verilator.md) and/or [FPGA](./setup_fpga.md) setup instructions.

### Running on-host DIF Tests

The Device Interface Function or [DIF](https://opentitan.org/book/sw/device/lib/dif/) libraries contain unit tests that run on the host and are built and run with Bazel.
As shown below, you may use Bazel to query which tests are available, build and run all tests, or build and run only one test.

#### Querying which tests are available
```console
bazel query 'tests(//sw/device/lib/dif:all)'
```

#### Building and running **all** tests
```console
bazel test //sw/device/lib/dif:all
```

#### Building and running a **single** test
For example, building and testing the UART DIF library's unit tests:
```console
bazel test //sw/device/lib/dif:uart_unittest
```

### Running on-host ROM Tests

Similar to the DIF libraries, you can query, build, and run all the [ROM](https://opentitan.org/book/sw/device/silicon_creator/rom/) unit tests (which also run on the host) with Bazel.

#### Querying which (on-host) tests are available
Note, the ROM has both on-host and on-device tests.
This query filters tests by their kind, i.e., only on-host tests.
```console
bazel query 'kind(cc_.*, tests(//sw/device/silicon_creator/lib/...))'
```

#### Building and running **all** (on-host) tests
```console
bazel test --test_tag_filters=-cw310,-dv,-verilator //sw/device/silicon_creator/lib/...
```

#### Building and running a **single** (on-host) test
For example, building and testing the ROM UART driver unit tests:
```console
bazel test //sw/device/silicon_creator/lib/drivers:uart_unittest
```

## Miscellaneous

### Bazel-built Software Artifacts

As described in the [OpenTitan Software](https://opentitan.org/book/sw/) documentation, there are three categories of OpenTitan software, all of which are built with Bazel. These include:
1. _device_ software,
1. _OTBN_ software,
1. _host_ software,

Bazel produces various artifacts depending on the category of software that is built.

#### Device Artifacts

Device software is built and run on OpenTitan hardware.
There are three OpenTitan "devices" for simulating/emulating OpenTitan hardware:
1. "sim\_dv": DV simulation (i.e., RTL simulation with commercial simulators),
1. "sim\_verilator": Verilator simulation (i.e., RTL simulation with the open source Verilator simulator),
1. "fpga\_cw310": FPGA.

Additionally, for each device, there are two types of software images that can be built, depending on the memory type the software is destined for, i.e.:
1. ROM,
1. flash,

To facilitate instantiating all build rules required to build the same artifacts across several devices and memories, we implement two OpenTitan-specific Bazel macros.
These macros include:
* `opentitan_rom_binary`
* `opentitan_flash_binary`

Both macros instantiate build rules to produce software artifacts for each OpenTitan device above.
Specifically, building either an `opentitan_rom_binary` or `opentitan_flash_binary` named `<target>`, destined to run on the OpenTitan device `<device>`, will output the following files under `bazel-out/`:
* `<target>_<device>.elf`: the linked program, in ELF format.
* `<target>_<device>.bin`: the linked program, as a plain binary with ELF debug information removed.
* `<target>_<device>.dis`: the disassembled program with inline source code.
* `<target>_<device>.logs.txt`: a textual database of addresses where `LOG_*` macros are invoked (for DV backdoor logging interface).
* `<target>_<device>.rodata.txt`: same as above, but contains the strings that are logged.
* `<target>_<device>.*.vmem`: a Verilog memory file which can be read by `$readmemh()` in Verilog code.
Note, `<device>` will be in {`sim_dv`, `sim_verilator`, `fpga_cw310`}.

Additionally, if the `opentitan_flash_binary` is signed, then these files will also be under `bazel-out/`:
* `<target>_<device>.<signing key name>.signed.bin`: the same `.bin` file above, but with a valid signature field in the manifest.
* `<target>_<device>.<signing key name>.signed.*.vmem`: the same `*.vmem` file above, but with a valid signature field in the manifest.

#### OTBN Artifacts

OTBN programs use a specialized build flow (defined in `rules/otbn.bzl`).
OTBN programs produce the following artifacts:
* `<target>.o`: unlinked object file usually representing a single assembly file
* `<target>.elf`: standalone executable binary representing one or more assembly/object files
* `<target>.rv32embed.{a,o}`: artifacts representing an OTBN binary, set up to be linked into a RISC-V program

In terms of Bazel rules:
* the `otbn_library` rule runs the assembler to create `<target>.o` artifacts, and
* the `otbn_binary` and `otbn_sim_test` rules run the linker on one or more `.o` files to create the `.elf` and `.rv32embed.{a,o}` artifacts.

Since OTBN has limited instruction memory, the best practice is to list each file individually as an `otbn_library`.
This way, binary targets can easily include only the files they need.

OTBN programs run on the OTBN coprocessor, unlike standard "on-device" programs that run on the main processor (Ibex).
There are two ways to run an OTBN program:
1. Run a standalone binary (`.elf`) on the specialized OTBN simulator.
1. Include a `.rv32embed` artifact in a C program that runs on Ibex, and create an on-device target as described in the previous section.

You can run `.elf` artifacts directly using the simulator as described in [the OTBN README](https://github.com/lowRISC/opentitan/blob/master/hw/ip/otbn/README.md#run-the-python-simulator).
The `otbn_sim_test` rule is a thin wrapper around `otbn_binary`.
If you use it, `bazel test` will run the OTBN simulator for you and check the test result.

To include an OTBN program in a C program, you need to add the desired OTBN `otbn_binary` Bazel target to the `deps` list of the C program's Bazel target.
No `#include` is necessary, but you will likely need to initialize the symbols from the OTBN program as required by the OTBN driver you are using.

#### Host Artifacts

Host software is built and run on the host hardware (e.g., an x64 Linux machine).
A final linked program in the ELF format is all that is produced for host software builds.
Note, the file will **not** have an extension.

### Disassembling Device Code

A disassembly of all executable sections is produced by the build system by default.
It can be found by looking for files with the `.dis` extension next to the corresponding ELF file.

```console
./bazelisk.sh build //sw/device/tests:uart_smoketest_prog_sim_verilator_dis

less "$(./bazelisk.sh outquery //sw/device/tests:uart_smoketest_prog_sim_verilator_dis)"
```

To get a different type of disassembly, e.g. one which includes data sections in addition to executable sections, objdump can be called manually.
For example the following command shows how to disassemble all sections of the UART DIF smoke test interleaved with the actual source code:

```console
./bazelisk.sh build --config=riscv32 //sw/device/tests:uart_smoketest_prog_sim_verilator.elf

riscv32-unknown-elf-objdump --disassemble-all --headers --line-numbers --source \
  "$(./bazelisk.sh outquery --config=riscv32 //sw/device/tests:uart_smoketest_prog_sim_verilator.elf)"
```

Refer to the output of `riscv32-unknown-elf-objdump --help` for a full list of options.

## Troubleshooting

### Check CI

First, [check the GitHub repository](https://github.com/lowRISC/opentitan/commits/master) to make sure the CI check is succeeding for the commit you cloned.
If there's an issue with that commit (it would have a red "X" next to it), check out the most recent commit that passed CI (indicated by a green check mark).
We try to always keep the main branch healthy, but the project is in active development and we're not immune to temporary breaks.

### Debugging a failed verilator test

If your `bazelisk.sh` build failed trying to run a test on Verilator, the first step is to see if you can build the chip simulation on its own:

```console
./bazelisk.sh build //hw:verilator
```
This build can take a long time; it's creating a simulation for the entire OpenTitan SoC.
Expect up to an hour for a successful build, depending on your machine.

If the `//hw:verilator` build above ran for a while and then failed with a bunch of warnings about various `.sv` files, it may have run out of RAM.
At the time of writing, our CI has 7GB of RAM, so that should be sufficient.
If your system is close to that limit, you may want to exit web browsers or other RAM-intensive applications while the Verilator build runs.

If the `//hw:verilator` build failed pretty much immediately, try running `util/check_tool_requirements.py` to make sure you meet the tool requirements.

If the `//hw:verilator` build succeeeded, but running a particular test fails, try running a different test (you can find many options under `sw/device/tests/`).
If that works, then it may be a problem with the specific test you're running.
See if you can build, but not run, the test with `./bazelisk.sh build` instead of `./bazelisk.sh test`.
If the test fails to build, that indicates some issue with the source code or possibly the RISC-V toolchain installation.
