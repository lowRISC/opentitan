{{% lowrisc-doc-hdr SW build flow }}

{{% toc 3 }}

## Overview
The centralized Makefile flow attempts to maximize reuse of commonly used
variables and rules among various software build targets (boot_rom, lib and
main software tests.

## Terminology / Some Make variables of interest
- **SW_ROOT_DIR**: The root directory for all of opentitan SW is sw/ and is
  indicated in the Make flow as `SW_ROOT_DIR`.

- **sw**: A 'software' (abbreviated as SW) is considered to be the top level
  SW application that is built through the final `vmem` image. For most tests, the
  targets are boot_rom and SW test application. Variables prefixed with `SW_`
  pertain to building the target SW application.

- **SW_SRCS**: The sources needed for compiling SW are indicated using the
  variable `SW_SRCS`.

- **SW_DIR**: The directory containing the SW sources is indicated using the
  variable `SW_DIR`. Note that `SW_DIR` is only the partial directory starting
  from the `SW_ROOT_DIR`. It is **mandatory** to set this variable on the command
  line.

- **SW_NAME**: A `SW_DIR` could contain one or more unique SW build targets.
  This variable is used to indicate which one is to be built, on the command
  line.

- **lib**: This refers to the library code generated from the shared common
  sources. These sources are currently placed in `sw/device/lib`, `sw/device/util` and
  `sw/device/exts` directories. More such directories can be added in future.
  Also, this is one of the goals of the make flow.

- **LIB_SRCS**: This is a list of all common / shared sources compiled into the
  lib archive. These include all of the required sources indicated in the
  directories listed above.

- **SW_BUILD_DIR**: This variable is the output directory to place all the
  generated output files. This includes object files, intermediate dependency
  files, generated linker scripts, elf, binary image, generated register header
  files, disassembled code, vmem, among other things. By default, this is set to
  the `SW_DIR`. It can be overridden on the command line. During compilation, the
  `SW_BUILD_DIR/lib` directory is created and is used to put all the object files
  and the archive file associated with `lib`.

The variables listed here are not exhaustive, but bare minimum to indicate to
the users the most typical use cases. Users are encouraged to read through
the files listed below for more details.

## Organization
The SW device build Makefiles are organized as follows:

- **`sw/device/Makefile`**: The top level SW build Makefile (`sw/device/Makefile`). All of the
  sub-make files are included directly or indirectly into this. This is the
  starting point for compiling any target.

- **`sw/device/opts.mk`**: All commonly used Make variables in one place. This sub-make
  file is also used to check if certain switches are enabled and further modify /
  customize the flow for target being built. An example of this is using the `TARGET`
  variable to change how SW is built for DV vs FPGA / Verilator / production SW.

- **`sw/device/rules.mk`**: All rules for generating all the outputs in one place.

These three form the *base-make files* for the SW build. Any directory containing
sources for building the SW needs to have an associated `srcs.mk` sub-make file
within that directory. These `srcs.mk` files are then required to be added to the
top level SW build Makefile.

- **`device/exts/common/srcs.mk`**: Additional extended common sources. This includes
    the default `CRT_SRCS` and the `LINKER_SCRIPT` which can be overridden for
    sw specific requirements.

- **`device/lib/srcs.mk`**: Directory containing sources to compile the lib elements and
  its dependencies.

- **`$(SW_DIR)/srcs.mk`**: This sub-make file contains sources for building a SW
  target is indicated using `SW_NAME`. This file is included in the top level
  SW build Makefile. Setting the **`SW_DIR` and `SW_NAME` correctly is
  required for building the desired image**. The existing variables in
  `opts.mk` can be overridden or appended to in this sub-make file to further
  customize the build target based on need. If this directory contains only a
  single SW build target, then `SW_NAME` can be set to the same name (typically
  same name as the directory and the C source) in this file. In that case, indicating
  `SW_NAME` on the command line is not required.

- **`device/exts/common/srcs.mk`**: Additional extended common sources. This includes
    the default `CRT_SRCS` and the `LINKER_SCRIPT` which can be overridden for
    sw specific requirements.

## How to build SW
The examples indicated below assume that the present working directory is
`$(SW_ROOT_DIR)/device`. As indicated in the previous sections, `SW_DIR` and `SW_NAME` are
mandatory variables that need to be set correctly on the command line. `SW_NAME`
is optional if `SW_DIR` has only one SW target and `SW_NAME` is set in
`$(SW_DIR)/srcs.mk` file. `SW_BUILD_DIR` is optional.

Build boot_rom:
```console
$ make SW_DIR=boot_rom SW_NAME=boot_rom
```

This will build the boot_rom image in the device/boot_rom directly itself. SW_NAME in
device/boot_rom/srcs.mk is already set to boot_rom, so there is no need to specify it
on the command line.

- Build the boot_rom in a separate build directory:
```console
$ make SW_DIR=boot_rom SW_BUILD_DIR=path/to/scratch
```

- Build hello_world test:
```console
$ make SW_DIR=examples/hello_world SW_NAME=hello_world SW_BUILD_DIR=path/to/scratch
```

- Build sha256 test:
```console
$ make SW_DIR=tests/hmac SW_NAME=sha256_test
```
