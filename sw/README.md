# OpenTitan Software

This subtree contains all software intended to run on the OpenTitan chip, as well as some tools.

## Building

OpenTitan software is built using [Meson](https://mesonbuild.com), although OpenTitan's project structure is sufficiently idiosyncratic that we use a custom workflow.

For example, to build the OpenTitan executable located at `sw/device/examples/hello_world` for FPGA, run the following commands:
```console
$ cd "$REPO_TOP"
$ ./meson_init.sh
$ ninja -C build-out sw/device/examples/hello_world/hello_world_export_fpga_nexysvideo
```

The resulting binaries will be located at `build-bin/sw/device/examples/hello_world`. For more information, check out [the relevant User Guide](../doc/ug/getting_started_sw.md).

The location of the RISC-V toolchain is /tools/riscv by default.
If your toolchain is located elsewhere set the `TOOLCHAIN_PATH` to that path before running `meson_init.sh`

```console
$ cd "$REPO_TOP"
$ export TOOLCHAIN_PATH=/path/to/toolchain
$ ./meson_init.sh
```
