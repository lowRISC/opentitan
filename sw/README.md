# OpenTitan Software

This subtree contains all software intended to run on the OpenTitan chip, as well as some tools.

## Building

OpenTitan software is built using [Meson](https://mesonbuild.com), although OpenTitan's project structure is sufficiently ideosyncratic that we use a custom workflow.

For example, to build the OpenTitan executable located at `sw/device/examples/hello_world` for FPGA, run the following commands:
```console
$ cd "$REPO_TOP"
$ ./meson_init.sh
$ ninja -C build-out/sw/fpga sw/device/examples/hello_world/hello_world_export
```

The resulting binaries will be located at `build-bin/sw/device/fpga/examples/hello_world`. For more information, check out [the relevant User Guide](../doc/ug/getting_started_sw.md).

