# OpenTitan top selection

The `hw/top` bazel package provides a mechanism to select the OpentTitan top for which all targets (headers, binaries, tests) are built. This package also provides various bazel targets to expose hardware information about the top that could be useful for software and bazel rules. Finally, its provides a number of useful bazel macros that integrate with the build system to handle conditional handling of dependencies.

**Table of content**
- [Top selection](#top-selection)
- [Bazel targets](#bazel-targets)
- [Common operations](#common-operations)

## Top selection

This package provide a single target `//hw/top:top` (which can abbreviated as `//hw/top`) which is a [`string_flat`](https://github.com/bazelbuild/bazel-skylib/blob/main/docs/common_settings_doc.md#string_flag). This means that:
- the top can be selected on bazel's command line using the syntax `--//hw/top=<top value>`,
- the top can be selected by any bazel [transition](https://bazel.build/rules/lib/builtins/transition).

The values accepted by this setting are the names of the tops configured with the build system. This includes, but is not limited to:
- `earlgrey`
- `darjeeling`
- `englishbreakfast`

The default value of this setting is `earlgrey`, meaning that unless explicitely specified, bazel will compile for Earlgrey.

For example, to build the UART headers for Darjeeling, use:
```console
./bazelisk.sh build --//hw/top=darjeeling //hw/top:uart_c_regs
```

## Bazel targets

The `//hw/top` package provides a number of important targets that expose information about the top, depending on the setting of `//hw/top:top`.

### Top library, linker script and defines

Each top's libraries is exposed as
- `//hw/top:top_lib`which is an alias to the actual top's library (e.g. `top_earlgrey.h`).
- `//hw/top:top_ld` which is an alias to the actual top's linker script (e.g. `top_earlgrey_memory.ld`).

Furthermore, adding `//hw/top:top_lib` or `//hw/top:top_ld` as a dependency of a C library or linker script will automatically make the following defines available:
- `OPENTITAN_IS_<TOPNAME>`: this define can be used for conditional compilation.

### C/Rust headers

The headers for every IP are exposed as:
- `//hw/top:<ip>_c_regs` for the C registers,
- `//hw/top:<ip>_rust_regs` for the rust registers.

[**Compatibility annotations**](#compatibility-annotations): those targets are only marked as compatible with the tops that contain at least an instance of them.

### Device Tables (DT)

The various DT artefacts are exposed as:
- `//hw/top:dt_api` for the generic DT API library (types and top level enums). This is a `cc_library`, in particular the plain source and header files are exposed as:
  - `//hw/top:dt_api_gen` for both the source and header files (`dt_api.h` and `dt_api.c`),
  - `//hw/top:dt_api_src` for the source file (`dt_api.c`),
  - `//hw/top:dt_api_hdr` for the header file (`dt_api.h`),
- `//hw/top:dt_<ip>` for each IP's DT library,
  - `//hw/top:dt_<ip>_gen` for both the source and header files (`dt_<ip>.h` and `dt_<ip>.c`),
  - `//hw/top:dt_<ip>_src` for the source file (`dt_<ip>.c`),
  - `//hw/top:dt_<ip>_hdr` for the header file (`dt_<ip>.h`),
- `//hw/top:dt_headers` for all DT headers (but not the implementation),
- `//hw/top:dt`for a target that depends on all DT items.

It is generally recommended that device code either depends on `//hw/top:dt` if they have many DT dependencies, or on the individual `//hw/top:dt_<ip>` if the want to be precise.

**Note:** `//hw/top:dt_api` depends on `//hw/top:top_lib` so that the top-level defines are available.

[**Compatibility annotations**](#compatibility-annotations): those targets are only marked as compatible with the tops that contain at least an instance of them.

### Top description

A complete description of the top is exposed as `//hw/top:top_desc`. This target provides a single `OpenTitanTopInfo` provider which can used by bazel rules to get access to top-specific information and files, such as Hjson files.

### Compatibility annotations

Bazel provides a mechanism under which targets can be [annotated](https://bazel.build/extending/platforms) to only be available when certain configuration settings are met. This prevents accidental errors such as using an Earlgrey header when compiling for Darjeeling. The `//hw/top` package makes extensive usage of this feature. Generally speaking, if a target does not make sense for a given `//hw/top` value, then it will be marked as [`@platforms//:incompatible`](https://bazel.build/extending/platforms#expressive-constraints) which will result in build errors.

For example, if we try to build Earlgrey headers for darjeeling:
```console
$ ./bazelisk.sh build //hw/top_earlgrey/sw/autogen:top_earlgrey --//hw/top=darjeeling
ERROR: Analysis of target '//hw/top_earlgrey/sw/autogen:top_earlgrey' failed; build aborted: Target //hw/top_earlgrey/sw/autogen:top_earlgrey is incompatible and cannot be built, but was explicitly requested.
Dependency chain:
    //hw/top_earlgrey/sw/autogen:top_earlgrey (927671)   <-- target platform (@@platforms//host:host) didn't satisfy constraint @@platforms//:incompatible
```

Note that this mechanism applies transitively, which has powerful consequences. For example, Darjeeling does not have a USB module. Let's look at what happens if try to compile to usbdev DIF for darjeeling:
```console
$ ./bazelisk.sh build //sw/device/lib/dif:usbdev --//hw/top=darjeeling
ERROR: Analysis of target '//sw/device/lib/dif:usbdev' failed; build aborted: Target //sw/device/lib/dif:usbdev is incompatible and cannot be built, but was explicitly requested.
Dependency chain:
    //sw/device/lib/dif:usbdev (927671)
    //sw/device/lib/dif/autogen:usbdev (927671)
    //sw/device/lib/dif/autogen:usbdev_src (927671)
    //sw/device/lib/dif/autogen:usbdev_gen (927671)   <-- target platform (@@platforms//host:host) didn't satisfy constraint @@platforms//:incompatible
```
As we can see, this DIF indirectly depends on generated top-specific code which does make sense on a platform without a usbdev and therefore bazel will not let us compile this target for Darjeeling.

You can create your own annotations by using the macros described in the next section.

## The `//hw/top:defs.bzl` library

This bazel library provides several important definitions are macros which can be used by rule creators and users to interact with the build system. See the documentation in [the file](https://github.com/lowRISC/opentitan/blob/master/hw/top/defs.bzl) for more details.
- `opentitan_if_ip(ip, obj, default)` provides a way to conditionally do something the top selected by `//hw/top` contains at least one instance of a given IP. For example, if we want to conditionally compile code only if the usbdev block is present, we could do:
Example:
```python
# Optional dependency on the usbdev with a define.
cc_library(
    name = "my_library",
    defines = opentitan_if_ip("usbdev", ["HAS_USBDEV"], []),
    deps = opentitan_if_ip("usbdev", ["//sw/device/lib/dif:usbdev"], []),
)
```
- `opentitan_require_ip(ip)` provides a way to construct a `target_compatible_with` restriction to indicate that a target is only valid if the top has at least one instance of a given IP. Recall that compatibility requirements are transitive so this annotation will usually be redundant if the target depends on headers or the DT. Example:
```python
cc_library(
    name = "my_library",
    target_compatible_with = opentitan_require_ip("uart"),
)
```
- `opentitan_select_top(values, default)` provides a way to conditionally do something depending on the top. For example if we to create an alias on another library on Earlgrey but a different one on Darjeeling and English Breakfast, we could do:
```python
alias(
    name = "my_alias",
    actual = opentitan_select_top({
    "earlgrey": "//something:earlgrey",
    ("englishbreakfast", "darjeeling"): "//something:dj_eb",
    }, "//something:default")
)
```
- `opentitan_require_top(top)` provides a way to construct a `target_compatible_with` restriction to indicate that a target is only valid on certan tops. Similarly to `opentitan_require_ip`, this requirement will usually be redundant if the target transitively depends on headers or the DT. Example:
```python
cc_library(
    name = "my_library",
    target_compatible_with = opentitan_require_top("darjeeling"),
)
```

## Common operations

This section explains how to perform several common operations using Bazel.

### Inspect the C/Rust/DT generated source code

The [bazel targets](#bazel-targets) compiles a lot of tool generated code which sometimes needs to be inspected. To access those files, you must perform the following two operations:
- build the file(s) using the correct `//hw/top` configuration,
- query the location of the output, **also** using the same `//hw/top` configuration.

For example to query the UART C headers for Darjeeling, run:
```console
$ ./bazelisk.sh build --//hw/top=darjeeling //hw/top:uart_c_regs
# NOTE that both commands use the same --//hw/top=darjeeling setting!
$ ./bazelisk.sh cquery --//hw/top=darjeeling //hw/top:uart_c_regs
bazel-out/k8-fastbuild/bin/hw/top/uart_regs.h
```
You can now open `bazel-out/k8-fastbuild/bin/hw/top/uart_regs.h` (path may vary between machines).

The DT headers and source have individual targets for technical reasons and should be queried using the following targets:
- `//hw/top:dt_api_src` for both the source file (`dt_api.c`),
- `//hw/top:dt_api_hdr` for both the header file (`dt_api.h`),
- `//hw/top:dt_<ip>_src` for both the source file (`dt_<ip>.c`),
- `//hw/top:dt_<ip>_hdr` for both the header file (`dt_<ip>.h`).

For example:
```console
$ ./bazelisk.sh build --//hw/top=darjeeling //hw/top:dt_uart_hdr
# NOTE that both commands use the same --//hw/top=darjeeling setting!
$ ./bazelisk.sh cquery --//hw/top=darjeeling //hw/top:dt_uart_hdr
bazel-out/k8-fastbuild/bin/hw/top/uart_regs.h
```
