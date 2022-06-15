---
title: Building (and Testing) Software
aliases:
    - /doc/ug/getting_started_build_sw
---

_Before following this guide, make sure you have read the_:
* main [Getting Started]({{< relref "getting_started" >}}) instructions, and
* [OpenTitan Software]({{< relref "sw/" >}}) documentation.

All OpenTitan software is built with [Bazel](https://bazel.build/).
Additionally, _most_ tests may be run with Bazel too.

## TL;DR
To install the correct version of bazel, build, and run all on-host tests you can simply run:

```console
$REPO_TOP/bazelisk.sh test //... --test_tag_filters=-cw310,-verilator --disk_cache=~/bazel_cache
```

## Installing Bazel

There are two ways to install the correct verion of Bazel:
1. **automatically**, using the `bazelisk.sh` script provided in the repo, or
1. **manually**.

### Automatic Installation

To simplify the installation of Bazel, and provide a means to seamlessly update the Bazel version we use in the future, we provide a shell script that acts as a wrapper for invocations of "`bazel ...`".
To use it, you two options:
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
sudo apt update && sudo apt install bazel-4.2.0
```

or by following [instructions for your system](https://bazel.build/install).

## Building Software with Bazel

Running
```console
bazel build //sw/...
```
will build all software in our repository.

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
* unit tests for device software, such as [DIF]({{< relref "/sw/device/lib/dif/README.md" >}}) and [mask ROM]({{< relref "/sw/device/silicon_creator/mask_rom/docs/" >}}) unit tests.
* any test for host software, such as `opentitan{lib,tool}`.

Examples of on-device tests are:
* [chip-level tests]({{< relref "/sw/device/tests/index.md" >}}).
* [mask ROM functional tests]({{< relref "/sw/device/silicon_creator/mask_rom/docs/" >}})

The remainder of this document will focus on building and running **on-host** tests with Bazel.
To learn about running **on-device** tests with Bazel, please continue back to the main [Getting Started]({{< relref "getting_started" >}}) instructions, and proceed with the [Verilator]({{< relref "setup_verilator" >}}) and/or [FPGA]({{< relref "setup_fpga" >}}) setup instructions.

### Running on-host DIF Tests

The Device Interface Function or [DIF]({{< relref "/sw/device/lib/dif/README.md" >}}) libraries contain unit tests that run on the host and are built and run with Bazel.
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

### Running on-host Mask ROM Tests

Similar to the DIF libraries, you can query, build, and run all the [mask ROM]({{< relref "/sw/device/silicon_creator/mask_rom/docs/" >}}) unit tests (which also run on the host) with Bazel.

#### Querying which (on-host) tests are available
Note, the mask ROM has both on-host and on-device tests.
This query filters tests by their kind, i.e., only on-host tests.
```console
bazel query 'kind(cc_.*, tests(//sw/device/silicon_creator/lib/...))'
```

#### Building and running **all** (on-host) tests
```console
bazel test --test_tag_filters=-cw310,-dv,-verilator //sw/device/silicon_creator/lib/...
```

#### Building and running a **single** (on-host) test
For example, building and testing the mask ROM UART driver unit tests:
```console
bazel test //sw/device/silicon_creator/lib/drivers:uart_unittest
```

## OpenTitan Bazel Workspace

The rules for Bazel are described in a language called Starlark, which looks a lot like Python.

The `$REPO_TOP` directory is defined as a Bazel workspace by the `//WORKSPACE` file.
`BUILD` files provide the information Bazel needs to build the targets in a directory.
`BUILD` files also manage any subdirectories that don't have their own `BUILD` files.

OpenTitan uses .bzl files to specify custom rules to build artifacts that require specific attention like on-device test rules and project specific binaries.

### WORKSPACE file

The `WORKSPACE` file controls external dependencies such that builds can be made reproducible and hermetic.
Bazel loads specific external dependencies, such as various language toolchains.
It uses them to build OpenTitan targets (like it does with bazel\_embedded) or to satisfy dependencies (as it does with abseil).
To produce increasingly stable releases the external dependencies loaded in `WORKSPACE` file attempts to fix a all external `http_archive`s to a specific SHA.
As we add more dependencies to the workspace, builds and tests will become less sensitive to external updates, and we will vastly simplify the [Getting Started]({{< relref "getting_started" >}}) instructions.

### BUILD files

Throughout the OpenTitan repository, `BUILD` files describe targets and dependencies in the same directory (and subdirectories that lack their own `BUILD` files).
`BUILD` files are mostly hand-written.
To maintain the invariant that hand-written files not be included in autogen directories, there are `BUILD` files that describe how to build and depend on auto-generated files in autogen subdirectories.

## Linting Software

There are several Bazel rules that enable running quality checks and fixers on code.
The subsections below describe how to use them.
All of the tools described below are run in CI on every pull request, so it is best to run them before committing code.

### Linting C/C++ Code
The OpenTitan supported linter for C/C++ files is `clang-format`.
It can be run with Bazel as shown below.

Run the following to check if all C/C++ code as been formatted correctly:
```console
bazel run //:clang_format_check
```
and run the following to fix it, if it is not formatted correctly.
```console
bazel run //:clang_format_fix
```

### Linting Starlark

The OpenTitan supported linter for Bazel files is `buildifier`.
It can be run with Bazel as shown below.

Run the following to check if all `WORKSPACE`, `BUILD`, and `.bzl` files have been formatted correctly:
```console
bazel run //:buildifier_check
```
and run the following to fix them, if they are not formatted correctly.
```console
bazel run //:buildifier_fix
```

### Checking License Headers

Lastly, the OpenTitan supported linter for checking that every source code file contains a license header may be run with:
```console
bazel run //:license_check
```

## Miscellaneous

### Bazel-built Artifacts

As decribed in the [OpenTitan Software]({{< relref "sw/" >}}) documentation, there are three categories of OpenTitan software, all of which are built with Bazel. These include:
1. _device_ software,
1. _OTBN_ software,
1. _host_ software,

Bazel produces various artifacts depending on the category of software that is built.

#### Device Artifacts

Device software is built and run on OpenTitan hardware.
There are three OpenTitan "devices" for simulating/emulating OpenTitan hardware:
1. DV simulation (i.e., RTL simulation with commercial simulators),
1. Verilator simulation (i.e., RTL simulation with the open source Verilator simulator),
1. FPGA.

Different software artifacts are built depending on the OpenTitan device above.
Specifically, building an executable `<target>` destined to run on the OpenTitan device `<device>` will output the following files under `bazel-out/`:
* `<target>_<device>`: the linked program, in ELF format.
* `<target>_<device>.bin`: the linked program, as a plain binary with ELF debug information removed.
* `<target>_<device>.elf.s`: the disassembled program with inline source code.
* `<target>_<device>.*.vmem`: a Verilog memory file which can be read by `$readmemh()` in Verilog code.

Note, `<device>` will be in {`sim_dv`, `sim_verilator`, `fpga_cw310`}, and `<target>` will end in the suffix "`_prog`" for executable images destined for flash.

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

You can run `.elf` artifacts directly using the simulator as described in [the OTBN README]({{< relref "/hw/ip/otbn/README/index.html#run-the-python-simulator">}}).
The `otbn_sim_test` rule is a thin wrapper around `otbn_binary`.
If you use it, `bazel test` will run the OTBN simulator for you and check the test result.

To include an OTBN program in a C program, you need to add the desired OTBN `otbn_binary` Bazel target to the `deps` list of the C program's Bazel target.
No `#include` is necessary, but you will likely need to initialize the symbols from the OTBN program as required by the OTBN driver you are using.

#### Host Artifacts

Host software is built and run on the host hardware (e.g., an x64 Linux machine).
A final linked program in the ELF format is all that is produced for host software builds.
Note, like the device ELF, the file will not have an extension.

### Disassembling Device Code

A disassembly of all executable sections is produced by the build system by default.
It can be found by looking for files with the `.elf.s` extension next to the corresponding ELF file.

To get a different type of disassembly, e.g. one which includes data sections in addition to executable sections, objdump can be called manually.
For example the following command shows how to disassemble all sections of the UART DIF smoke test interleaved with the actual source code:

```console
riscv32-unknown-elf-objdump --disassemble-all --headers --line-numbers --source \
  $(find -L bazel-out/ -type f -name "uart_smoketest_prog_sim_verilator")
```

Refer to the output of `riscv32-unknown-elf-objdump --help` for a full list of options.

### Locating Bazel-built Artifacts

Bazel built artifacts can be located in the symlinked `bazel-out/` directory that gets automatically created on invocations of Bazel.
To locate build artifacts, you may use the `find` utility.
For example, after building the UART smoke test device software with
```console
bazel build //sw/device/tests:uart_smoketest_sim_verilator
```
to locate the `.bin` file use
```console
find -L bazel-bin/ -type f -name "uart_smoketest_prog_sim_verilator.bin"
```

### Troubleshooting Builds

If you encounter an unexplained error building or running any `bazel` commands, you can issue a subsequent `bazel clean` command to erase any existing building directories to yield a clean build.
Specifically, according to the Bazel [documentation](https://docs.bazel.build/versions/main/user-manual.html#clean), issuing a
```console
bazel clean
```
deletes all the output build directories, while running a
```console
bazel clean --expunge
```
will wipe all disk and memory traces (i.e., any cached intermediate files) produced by Bazel.
The latter sledgehammer is only intended to be used as a last resort when the existing configuration is seriously broken.

### Disk Cache

Bazel can use a directory on the file system as a remote cache.
This is useful for sharing build artifacts across multiple [`git` worktrees](https://git-scm.com/docs/git-worktree) or multiple workspaces of the same project, such as multiple checkouts.

Use the `--disk_cache=<filename>` to specify a cache directory.
For example, running
```console
bazel build //... --disk_cache=~/bazel_cache
```
will cache all built artifacts.

Alternatively add the following to `$HOME/.bazelrc` to avoid having automatically use the disk cache on every Bazel invocation.
```
build --disk_cache=~/bazel_cache
```

For more documentation on Bazel disk caches see the [official documentation](https://docs.bazel.build/versions/main/remote-caching.html#disk-cache).

### Excluding Verilator Simulation Binary Builds

Many device software targets depend on the Verilator simulation binary,
The Verilator simulation binary is slow to build.
To avoid building it, use the
`--define DISABLE_VERILATOR_BUILD=true` build option.
For example, to build the UART smoke test artifacts but not the Verilator simulation binary run
```console
bazel build --define DISABLE_VERILATOR_BUILD=true //sw/device/tests:uart_smoketest
```
