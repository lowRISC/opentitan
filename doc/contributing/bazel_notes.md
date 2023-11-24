# Bazel Notes

Both OpenTitan hardware and software is built with Bazel.
While our [Getting Started](../../doc/getting_started/README.md) guides detail some of the Bazel commands that can be used to build both types of artifacts, below are detailed notes on:
* how Bazel is configured for our project, and
* brief examples of Bazel commands that are useful for:
    * querying,
    * building, and
    * running tests with Bazel.

# OpenTitan Bazel Workspace

The rules for Bazel are described in a language called Starlark, which looks a lot like Python.

The `$REPO_TOP` directory is defined as a Bazel workspace by the `//WORKSPACE` file.
`BUILD` files provide the information Bazel needs to build the targets in a directory.
`BUILD` files also manage any subdirectories that don't have their own `BUILD` files.

OpenTitan uses .bzl files to specify custom rules to build artifacts that require specific attention like on-device test rules and project specific binaries.

## WORKSPACE file

The `WORKSPACE` file controls external dependencies such that builds can be made reproducible and hermetic.
Bazel loads specific external dependencies, such as various language toolchains.
It uses them to build OpenTitan targets (like it does with bazel\_embedded) or to satisfy dependencies (as it does with abseil).
To produce increasingly stable releases the external dependencies loaded in `WORKSPACE` file attempts to fix a all external `http_archive`s to a specific SHA.
As we add more dependencies to the workspace, builds and tests will become less sensitive to external updates, and we will vastly simplify the [Getting Started](../../doc/getting_started/README.md) instructions.

## BUILD files

Throughout the OpenTitan repository, `BUILD` files describe targets and dependencies in the same directory (and subdirectories that lack their own `BUILD` files).
`BUILD` files are mostly hand-written.
To maintain the invariant that hand-written files not be included in autogen directories, there are `BUILD` files that describe how to build and depend on auto-generated files in autogen subdirectories.

# General Commands

- Build everything (software and Verilator hardware):
  ```sh
  bazel build //...
  ```
- Build and run all tests (on-host tests, and Verilator/FPGA on-device tests):
  ```sh
  bazel test --test_tag_filters=-broken,-dv //sw/...
  ```
  Note: this will take several hours.
- Clean all build outputs and reclaim all disk and memory traces of a Bazel instance:
  ```sh
  bazel clean --expunge
  ```
  Note: you should rarely need to run this, see [below](#troubleshooting-builds) for when this may be necessary.

# Locating Build Artifacts

When Bazel builds a target, or the dependencies of a target, it places them in a Bazel-managed output directory.
This can make them difficult to find manually, however, Bazel also provides a mechanism to query for built artifacts that is demonstrated below.
Note, the `outquery-*` command shown below is a special command that is parsed via our `bazelisk.sh` script.
Therefore, it cannot be run with a standalone `bazel ...` invocation.

## `opentitan_{rom,flash}_binary` Artifacts

- Query the locations of all Bazel-built artifacts for all OpenTitan devices for an `opentitan_{rom,flash}_binary` macro:
  ```sh
  ./bazelisk.sh outquery-all <target>
  ```
- Query the locations of all Bazel-built artifacts for a specific OpenTitan device for an `opentitan_{rom,flash}_binary` macro:
  ```sh
  ./bazelisk.sh outquery-all <target>_<device>
  ```
  Note: `<device>` will be in {`sim_dv`, `sim_verilator`, `fpga_cw310`}.

See [Building (and Testing) Software](../getting_started/build_sw.md#device-artifacts), device software can be built for multiple OpenTitan devices and memories, using OpenTitan-specific Bazel macros.

## `opentitan_functest` Artifacts

As described [Building (and Testing) Software](../getting_started/build_sw.md#device-artifacts), device software can be built for multiple OpenTitan devices and memories, using OpenTitan-specific Bazel macros.
Since running tests on multiple OpenTitan devices (whether DV or Verilator simulation, or an FPGA) involves building several software images for multiple memories, we provide a Bazel macro for this.
This macro is called `opentitan_functest`.

- List all `sh_test` targets instantiated by a `opentitan_functest`, e.g. the UART smoketest:
  ```sh
  bazel query 'labels(tests, //sw/device/tests:uart_smoketest)'
  ```
- Query the HW and SW dependencies of a specific `opentitan_functest` for the `fpga_cw310` device, e.g. the UART smoketest:
  ```sh
  bazel query 'labels(data, //sw/device/tests:uart_smoketest_fpga_cw310)'
  ```
  or for any `opentitan_functest` target and `<device>` in {`sim_dv`, `sim_verilator`, `fpga_cw310`}
  ```sh
  bazel query 'labels(data, <target>_<device>)'
  ```
- Query the software artifacts built for the `opentitan_flash_binary` that is a dependency of an `opentitan_functest` for the `fpga_cw310` device, e.g. the UART smoketest:
  ```sh
  bazel query 'labels(srcs, //sw/device/tests:uart_smoketest_prog_fpga_cw310)'
  ```
  or for any `opentitan_functest` `<target>` and `<device>` in {`sim_dv`, `sim_verilator`, `fpga_cw310`}
  ```sh
  bazel query 'labels(srcs, <target>_prog_<device>)'
  ```
  Note: if an `opentitan_functest` target has the name `foo`, then the `opentitan_flash_binary` target that is instantiated by the `opentitan_functest` will be named `foo_prog_<device>`.

# Building Software

* To build OpenTitan software see [here](../getting_started/build_sw.md#building-software-with-bazel), or run
  ```sh
  bazel build <target>
  ```

# Testing Software

## On-Host Tests

* To query-for/run *on-host* software tests see [here](../getting_started/build_sw.md#running-tests-with-bazel).

## On-Device Tests

All device software, regardless of the device, is built with Bazel.
However, only Verilator simulation and FPGA device software tests can be run with Bazel.

### ROM Tests

* Query for all ROM functional and E2E tests for FPGA:
  ```sh
  bazel query 'filter(".*_fpga_cw310", kind(".*test rule", //sw/device/silicon_creator/...))'
  ```
  and for Verilator:
  ```sh
  bazel query 'filter(".*_sim_verilator", kind(".*test rule", //sw/device/silicon_creator/...))'
  ```
* Run all ROM functional and E2E tests on FPGA:
  ```sh
  bazel test --test_tag_filters=cw310 //sw/device/silicon_creator/...
  ```
  and for Verilator:
  ```sh
  bazel test --test_tag_filters=verilator //sw/device/silicon_creator/...
  ```
* Run a single ROM functional or E2E test on FPGA and see the output in real time:
  ```sh
  bazel test \
    --define DISABLE_VERILATOR_BUILD=true \
    --test_tag_filters=cw310 \
    --test_output=streamed \
    //sw/device/silicon_creator/lib:boot_data_functest
  ```
  or, remove the define/filtering flags and just append the `<device>` name like:
  ```sh
  bazel test --test_output=streamed //sw/device/silicon_creator/lib:boot_data_functest_fpga_cw310
  ```
  and similarly for Verilator:
  ```sh
  bazel test --test_output=streamed //sw/device/silicon_creator/lib:boot_data_functest_sim_verilator
  ```

### Chip-Level Tests

* Query for all chip-level tests for FPGA:
  ```sh
  bazel query 'filter(".*_fpga_cw310", kind(".*test rule", //sw/device/tests/...))'
  ```
  and for Verilator:
  ```sh
  bazel query 'filter(".*_sim_verilator", kind(".*test rule", //sw/device/tests/...))'
  ```
* Run all chip-level tests on FPGA:
  ```sh
  bazel test --define DISABLE_VERILATOR_BUILD=true --test_tag_filters=cw310 //sw/device/tests/...
  ```
  and for Verilator:
  ```sh
  bazel test --test_tag_filters=verilator //sw/device/tests/...
  ```
* Run a single chip-level test on FPGA and see the output in real time:
  ```sh
  bazel test \
    --define DISABLE_VERILATOR_BUILD=true
    --test_tag_filters=cw310 \
    --test_output=streamed \
    //sw/device/tests:uart_smoketest
  ```
  or, remove the define/filtering flags and just append the `<device>` name like:
  ```sh
  bazel test --test_output=streamed //sw/device/tests:uart_smoketest_fpga_cw310
  ```
  and similarly for Verilator:
  ```sh
  bazel test --test_output=streamed //sw/device/tests:uart_smoketest_sim_verilator
  ```

# Linting Software

There are several Bazel rules that enable running quality checks and fixers on code.
They can be listed by running the following:
```sh
bazel query //quality:all
```
The subsections below describe how to use them.
All of the tools described below are run in CI on every pull request, so it is best to run them before committing code.

## Linting C/C++ Code

The OpenTitan supported linter for C/C++ files is `clang-format`.
It can be run with Bazel as shown below.

Run the following to check if all C/C++ code as been formatted correctly:
```sh
bazel test //quality:clang_format_check --test_output=streamed
```
and run the following to fix it, if it is not formatted correctly.
```sh
bazel run //quality:clang_format_fix
```

## Formatting Rust Code

The OpenTitan project uses `rustfmt` to format Rust code.
It can be run with Bazel as shown below.

Run the following to check if all Rust code as been formatted correctly:
```sh
bazel test //quality:rustfmt_check --test_output=streamed
```
and run the following to fix it, if it is not formatted correctly.
```sh
bazel run //quality:rustfmt_fix
```

## Formatting Bazel files

The OpenTitan project uses `buildifier` to automatically format Bazel files.

Run the following to check if all BUILD files has been formatted correctly:
```sh
bazel test //quality:buildifier_check --test_output=streamed
```
and run the following to fix it, if it is not formatted correctly.
```sh
bazel run //quality:buildifier_fix
```

## Linting Starlark

The OpenTitan supported linter for Bazel files is `buildifier`.
It can be run with Bazel as shown below.

Run the following to check if all `WORKSPACE`, `BUILD`, and `.bzl` files have been formatted correctly:
```sh
bazel test //quality:buildifier_check --test_output=streamed
```
and run the following to fix them, if they are not formatted correctly.
```sh
bazel run //quality:buildifier_fix
```

## Checking License Headers

Lastly, the OpenTitan supported linter for checking that every source code file contains a license header may be run with:
```sh
bazel run //quality:license_check --test_output=streamed
```

# Building Hardware

Note, to run (software) tests on these OpenTitan hardware platforms **does not** require these Bazel commands be invoked before the test commands above.
Bazel is aware of all dependency relationships, and knows what prerequisites to build to run a test.

- Build FPGA bitstream with (test) ROM, see [here](../getting_started/setup_fpga.md#build-an-fpga-bitstream).
- Build FPGA bitstream with (production) ROM, see [here](../getting_started/setup_fpga.md#build-an-fpga-bitstream).
- Build Verilator simulation binary:
  ```sh
  bazel build //hw:verilator
  ```

# Miscellaneous

## Troubleshooting Builds

If you encounter an unexplained error building or running any `bazel` commands, you can issue a subsequent `bazel clean` command to erase any existing building directories to yield a clean build.
Specifically, according to the Bazel [documentation](https://docs.bazel.build/versions/main/user-manual.html#clean), issuing a
```sh
bazel clean
```
deletes all the output build directories, while running a
```sh
bazel clean --expunge
```
will wipe all disk and memory traces (i.e., any cached intermediate files) produced by Bazel.
The latter sledgehammer is only intended to be used as a last resort when the existing configuration is seriously broken.

## Create a `.bazelrc` File

Create a `.bazelrc` file in your home directory to simplify executing bazel commands.
For example, you can use a `.bazelrc` to:
* set up a [disk cache](#disk-cache), or
* skip running tests on the CW310 FPGA if you don not have one.

A `.bazelrc` file that would accomplish this would look like:
```
# Make Bazel use a local directory as a remote cache.
build --disk_cache=~/bazel_cache

# Skip CW310 FPGA tests, since I do not have said FPGA.
test --test_tag_filters=-cw310
```

See the [`.bazelrc`](https://github.com/lowRISC/opentitan/blob/master/.bazelrc) file in the OpenTitan repository for more examples.
Additionally, for more information see the Bazel [documentation](https://bazel.build/run/bazelrc).

### Site-specific `.bazelrc-site` options

We use the term "compute site" to refer to a particular development host, or more broadly a _collection_ of compute nodes, that is operated by an organization with its own unique compute requirements or IT policies.
The experience of working in such an environment may be different than using an off-the-shelf Linux distribution, and so team members working on some compute sites may require the use of slightly different Bazel options.

In addition to each user's `$HOME/.bazelrc` file and the project-level configurations in [`$REPO_TOP/.bazelrc`](https://github.com/lowRISC/opentitan/blob/master/.bazelrc), there is the option to add site-specific configuration options, by adding them to the file `$REPO_TOP/.bazelrc-site`.

The `.bazelrc-site` file can be useful for enforcing site-specific policies such as:
- Default locations for build artifacts (e.g., new defaults for `--output_user_root` or perhaps `--output_base` options, outside the `$HOME` filesystem).
- Site-specific, non-standard paths for build-tools, libraries, or package configuration data.

Putting Bazel options in this file adds another layer of configuration to help groups of individuals working on a common compute site share the same site-specific default options.

At a more fine-grained level, individual users can still place options in `$HOME/.bazelrc`, potentially overriding the options used in `.bazelrc-site` and `$REPO_TOP/.bazelrc`.
However the "$HOME/.bazelrc" file is not specific to OpenTitan, which could create confusion for users working on a number of projects.

The policies and paths for each contributing site could vary greatly.
So in order to avoid accidental conflicts between sites, the `.bazelrc-site` file is explicitly _not_ included in the git repository and OpenTitan CI scripts will reject any commit that includes a `.bazelrc-site` file.

## Disk Cache

Bazel can use a directory on the file system as a remote cache.
This is useful for sharing build artifacts across multiple [`git` worktrees](https://git-scm.com/docs/git-worktree) or multiple workspaces of the same project, such as multiple checkouts.

Use the `--disk_cache=<filename>` to specify a cache directory.
For example, running
```sh
bazel build //... --disk_cache=~/.cache/bazel-disk-cache
```
will cache all built artifacts.
Alternatively add the following to `$HOME/.bazelrc` to avoid having automatically use the disk cache on every Bazel invocation, as shown [above](#create-a-bazelrc-file).

Note that Bazel does not perform any garbage collection on the disk cache.
To clean out the disk cache, you can set a cron job to periodically delete all files that have not been accessed for a certain amount of time.
For example add the following line with the path to your disk cache to your crontab (using `crontab -e`) to delete all files that were last accessed over 60 days ago.

```sh
0 0 * * 0 /usr/bin/find /path/to/disk/cache -type f -atime +60 -delete
```

For more documentation on Bazel disk caches see the [official documentation](https://docs.bazel.build/versions/main/remote-caching.html#disk-cache).

## Excluding Verilator Simulation Binary Builds

Many device software targets depend on the Verilator simulation binary,
The Verilator simulation binary is slow to build.
To avoid building it, use the
`--define DISABLE_VERILATOR_BUILD=true` build option.
For example, to build the UART smoke test artifacts but not the Verilator simulation binary run
```sh
bazel build --define DISABLE_VERILATOR_BUILD=true //sw/device/tests:uart_smoketest
```

## Displaying Test Outputs in Real Time

By default, Bazel does not write test outputs to STDOUT.
To see a test's output in real time, use the `--test_output=streamed` flag, like:
```sh
bazel test --test_output=streamed //sw/device/tests:uart_smoketest_fpga_cw310
```

## Filtering Broken Tests

Some tests are marked known to be broken (and are in the process of being triaged).
To prevent running these tests when running a block of tests, use the `test_tag_filters=-broken` flag.
For example, to run all chip-level tests except the broken ones on FPGA:
```sh
bazel test --test_tag_filters=cw310,-broken //sw/device/tests/...
```

## Using Bazel with Git Worktrees

Bazel was not optimized for the `git` worktree workflow, but using worktrees can help with branch management and provides the advantage of being able to run multiple Bazel jobs simultaneously.
Here are some tips that can improve the developer experience when using worktrees.

1. Follow the [instructions above](#disk-cache) to enable the disk cache.
  Bazel uses the workspace's path when caching actions.
  Because each worktree is a separate workspace at a different path, different worktrees cannot share an action cache.
  They can, however, share a disk cache, which helps avoid rebuilding the same artifacts across different worktrees.
  Note that the repository cache is shared by default across all workspaces, so no additional configuration is needed there.
1. Before deleting a worktree, be sure to run `bazel clean --expunge` to remove Bazel's generated files.
  Otherwise, files from old worktrees can accumulate in your output user root (located at `~/.cache/bazel/_bazel_${USER}/` by default).

## Commonly Encountered Issues

### Cannot find ld

One issue encountered while using bazel is the following error message when attempting to build:
```sh
  = note: collect2: fatal error: cannot find 'ld'
          compilation terminated.
```

The reason this occurs is related to these issues:
* [opentitan issue](https://github.com/lowRISC/opentitan/issues/12448)
* [rust issue](https://github.com/bazelbuild/rules_rust/issues/1114)

Specifically, when the rustc compiler is invoked, it uses the LLVM linker that is not managed by the bazel flow.
This means bazel cannot ensure it is installed at a specific location, and instead just uses whatever is available on the host machine.
The issue above points out that rustc expects the linker to be located in the same directory as `gcc`, so if on the host machine this statement is untrue, there can be build issues.

To resolve this problem, you can either:
1. Install the LLVM linker with, e.g., `sudo apt install lld`.
2. Symlink `lld` to where `gcc` is installed.

or,
1. add the build flag `--@rules_rust//:extra_rustc_toolchain_dirs=/path/to/somewhere/else` to your `.bazelrc-site` file to specify a different location on your system where host toolchain tools may be found.

Either of these workarounds will be needed until the `rules_rust` issue is resolved.
