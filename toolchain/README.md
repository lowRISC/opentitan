# OpenTitan RISC-V toolchain

This directory contains the Bazel configuration for OpenTitan's RISC-V
toolchain.

This LLVM toolchain comes from the [lowrisc-toolchains] repository. See
`third_party/lowrisc/BUILD.lowrisc_toolchain.bazel` for changing the toolchain
version.

[lowrisc-toolchains]: https://github.com/lowRISC/lowrisc-toolchains

## Configuration

There are four rules used to configure the toolchain:

1. `cc_toolchain`: groups flags, features, and tools into a toolchain.
2. `cc_tool_map`: assigns tools to actions.
3. `cc_args`: defines flags to add to tools based on actions.
3. `cc_feature`: allows `cc_args` flags to be conditionally enabled.

To add new flags to a tool in the toolchain, define a new `cc_args` target
and assign it to some actions (e.g. compiling C code, linking, etc.). Add the
new flags to `cc_toolchain.args`.

To make flags optional, define a new `cc_feature` for those `cc_args`. Features
can be enabled at the command line using `bazel --features=$feature_name`. Add
the flags to `cc_toolchain.known_features` and optionally to
`cc_toolchain.enabled_features`.

Bazel has three built-in features called `dbg`, `fastbuild`, and `opt` that can
be used to enable and disable flags at different optimization levels.
