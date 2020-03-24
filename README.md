# bazel-embedded
**Caution:** This is alpha quality software at the moment and has not be tested in depth.
bazel-embedded is a set of tools that enable embedded development using bazel. 

Current support is limited to Arm Cortex-M Devices:
- Cortex M0
- Cortex M1
- Cortex M3
- Cortex M4
- Cortex M7

## What is included
Currently only toolchains are included in this repository. The end goal is to have this package come "batteries included" and with;
- Static analysers 
- A collection of BUILD file templates for common embedded libraries
- Utilities for programming targets
- Utilities for debugging targets
- Parralell execution for a test "farm" of embedded test devices

## Getting started
Add the following to your WORKSPACE file


```py
load("@bazel_tools//tools/build_defs/repo:git.bzl", "git_repository")

git_repository(
    name = "bazel_embedded",
    commit = "d0d4bfacb47bd2db67f558adc69149b4d5a915ab",
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

## Caveats
If your repository contains platform independant you will not be able to automatically exclude platform dependant code. For example;
package/BUILD
```py
cc_library(
    name = "can_run_on_microcontroller_only"
    ...
)
cc_library(
    name = "can_run_on_anything"
    ...
)
```
You may compile for your host;
```sh
bazel build //package:can_run_on_anything
```
You may cross compile for your microcontroller
```sh
bazel build //package/... --platforms=@bazel_embedded//platforms:cortex_m7_fpu
```
But automated skipping of targets based on compatibility is not supported. So bazel will happily attempt to compile the //package:can_run_on_microcontroller_only using your host compiler, which in almost all cases will fail.
```sh
bazel build //package/... 
```
