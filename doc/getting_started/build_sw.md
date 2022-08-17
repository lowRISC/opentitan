---
title: Building (and Testing) Software
aliases:
    - /doc/ug/getting_started_build_sw
---

_Before following this guide, make sure you have read the_:
* main [Getting Started]({{< relref "getting_started" >}}) instructions,
* install Verilator section of the [Verilator guide]({{< relref "setup_verilator.md" >}}), and
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
* unit tests for device software, such as [DIF]({{< relref "/sw/device/lib/dif" >}}) and [ROM]({{< relref "/sw/device/silicon_creator/rom/docs/" >}}) unit tests.
* any test for host software, such as `opentitan{lib,tool}`.

Examples of on-device tests are:
* [chip-level tests]({{< relref "/sw/device/tests/index.md" >}}).
* [ROM functional tests]({{< relref "/sw/device/silicon_creator/rom/docs/" >}})

The remainder of this document will focus on building and running **on-host** tests with Bazel.
To learn about running **on-device** tests with Bazel, please continue back to the main [Getting Started]({{< relref "getting_started" >}}) instructions, and proceed with the [Verilator]({{< relref "setup_verilator" >}}) and/or [FPGA]({{< relref "setup_fpga" >}}) setup instructions.

### Running on-host DIF Tests

The Device Interface Function or [DIF]({{< relref "/sw/device/lib/dif" >}}) libraries contain unit tests that run on the host and are built and run with Bazel.
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

Similar to the DIF libraries, you can query, build, and run all the [ROM]({{< relref "/sw/device/silicon_creator/rom/docs/" >}}) unit tests (which also run on the host) with Bazel.

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

To get a different type of disassembly, e.g. one which includes data sections in addition to executable sections, objdump can be called manually.
For example the following command shows how to disassemble all sections of the UART DIF smoke test interleaved with the actual source code:

```console
riscv32-unknown-elf-objdump --disassemble-all --headers --line-numbers --source \
  $(find -L bazel-out/ -type f -name "uart_smoketest_prog_sim_verilator")
```

Refer to the output of `riscv32-unknown-elf-objdump --help` for a full list of options.
