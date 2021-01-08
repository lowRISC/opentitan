# bazel-embedded

![CI](https://github.com/silvergasp/bazel-embedded/workflows/CI/badge.svg)


<img src="https://upload.wikimedia.org/wikipedia/en/7/7d/Bazel_logo.svg" alt="drawing" width="200"/>

At this point it is relatively easy to add support for new architectures, that have gcc based compilers. In future we will be adding clang support, so that we can make use of clangs static-analyzers. If you would like an architecture added to this repository let us know.

Currently supported hosts:
- Windows
- Mac/Unix
- Linux

Current support is limited to Arm Cortex-M Devices:
- Cortex M0
- Cortex M1
- Cortex M3
- Cortex M4 (with/out fpu)
- Cortex M7 (with/out fpu)

## What is included
List of support;
- [x] Toolchains
- [ ] Static analysers 
- [X] A collection of BUILD file templates for common embedded libraries
- [x] Utilities for programming targets
- [x] Utilities for debugging targets
- [ ] Parralell execution for a test "farm" of embedded test devices

## Getting started
Add the following to your WORKSPACE file


```py
load("@bazel_tools//tools/build_defs/repo:git.bzl", "git_repository")

git_repository(
    name = "bazel_embedded",
    commit = "6e32163e00c3789d059fa4e25f653d92647b31b1",
    remote = "https://github.com/silvergasp/bazel-embedded.git",
    shallow_since = "1585022166 +0800",
)

load("@bazel_embedded//:bazel_embedded_deps.bzl", "bazel_embedded_deps")

bazel_embedded_deps()

load("@bazel_embedded//platforms:execution_platforms.bzl", "register_platforms")

register_platforms()

load(
    "@bazel_embedded//toolchains/compilers/gcc_arm_none_eabi:gcc_arm_none_repository.bzl",
    "gcc_arm_none_compiler",
)

gcc_arm_none_compiler()

load("@bazel_embedded//toolchains/gcc_arm_none_eabi:gcc_arm_none_toolchain.bzl", "register_gcc_arm_none_toolchain")

register_gcc_arm_none_toolchain()
```

Add the following to your .bazelrc file
```
# Enable toolchain resolution with cc
build --incompatible_enable_cc_toolchain_resolution
```

Cross Compile your target

```sh
bazel build //:your_target --platforms=@bazel_embedded//platforms:cortex_m0
bazel build //:your_target --platforms=@bazel_embedded//platforms:cortex_m1
bazel build //:your_target --platforms=@bazel_embedded//platforms:cortex_m3
bazel build //:your_target --platforms=@bazel_embedded//platforms:cortex_m4
bazel build //:your_target --platforms=@bazel_embedded//platforms:cortex_m7
bazel build //:your_target --platforms=@bazel_embedded//platforms:cortex_m4_fpu
bazel build //:your_target --platforms=@bazel_embedded//platforms:cortex_m7_fpu
```

Explore the examples for more in depth details...

You may choose to upload your code to a microcontroller using the [openocd](tools/openocd/README.md) package which allows you to program using SWD or JTAG. An example of this is shown below;

BUILD

```python
load("@rules_cc//cc:defs.bzl", "cc_binary")
load("@bazel_embedded//tools/openocd:defs.bzl", "openocd_debug_server", "openocd_flash")

# This target can be run to launch a gdb server on port 3333
openocd_debug_server(
    name = "main_debug_server",
    device_configs = [
        "target/stm32h7x_dual_bank.cfg",
    ],
    interface_configs = [
        "interface/stlink.cfg",
    ],
    transport = "hla_swd",
)
# The target to flash
cc_binary(
    name = "main",
    srcs = ["main.cc"],
    linkopts = [
        # app_code.ld is a linker script in the same directory
        "-T $(location :app_code.ld)",
        "-lc",
        "-lm",
        "-lnosys",
        "-u _printf_float",
    ],
    visibility = ["//visibility:public"],
    deps = [
        ":app_code.ld",
        "//libs/cpp/board_support:board_support_package",
    ],
)
# Run this target to upload to the microcontroller
openocd_flash(
    name = "main_flash",
    device_configs = [
        "target/stm32h7x_dual_bank.cfg",
    ],
    image = ":main.stripped",
    interface_configs = [
        "interface/stlink.cfg",
    ],
    transport = "hla_swd",
)
```

Alternatively, an execution wrapper can be used to execute a binary on an embedded target using openocd, and bazel's `--run_under` command line option.

BUILD
```python
load("@bazel_embedded//tools/openocd:defs.bzl", "openocd_execution_wrapper")

openocd_execution_wrapper(
    name = "test_wrapper",
    baud_rate = "115200",
    device_configs = [
        "target/stm32h7x_dual_bank.cfg",
    ],
    fail_string = "FAILED",
    interface_configs = [
        "interface/stlink.cfg",
    ],
    port = "/dev/ttyACM0",
    success_string = "PASSED",
    transport = "hla_swd",
)
```
```sh
bazel run //:your_target --platforms=@bazel_embedded//platforms:cortex_m7_fpu --run_under=//:test_wrapper
bazel test //:your_target --platforms=@bazel_embedded//platforms:cortex_m7_fpu --run_under=//:test_wrapper
```
This will pipe the serial output from the microcontroller over /dev/ttyACM0 to stdout. If a line contains 'PASSED', the wrapper will return 0, if a line contains 'FAILED' the wrapper will return 1. This is useful if you are wrapping a cc_test. If success_string or fail_string is not specified, the wrapper will not exit unless sent a sigterm (e.g. by CTRL-C). Leaving these empty can be useful when wrapping a standard cc_binary.

## Feature configuration
Bazel can be configured using [features](https://docs.bazel.build/versions/master/cc-toolchain-config-reference.html#features). Each toolchain in this repository aims to implement a consistent behaviour for a given set of features. The list of available configuration features can be listed using the following command.
```bash
bazel run @bazel_embedded//toolchains/features:print_all_features
```
From here you may use each feature from the command line, the following example enables all warnings as errors and optimises for release;
```bash
bazel build //toolchains/compilation_tests/... --platforms=@bazel_embedded//platforms:cortex_m0 --features=all_warnings_as_errors,opt
```
