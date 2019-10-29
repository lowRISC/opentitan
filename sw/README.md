# OpenTitan Software

This subtree contains all software intended to run on the OpenTitan chip, as well as some tools.

## Building

OpenTitan software is built using [Meson](https://mesonbuild.com).
For example, to build the OpenTitan executable located at `device/examples/hello_world/hello_world.bin`, run the following commands:
```sh
cd "${REPO_TOP}"
./meson-init.sh -r
ninja -C build-"${TARGET}" device/examples/hello_world/hello_world.bin
```
`$TARGET` should be one of `verilator` or `fpga`, depending on whether the executable should be built to run under simulation or on a phyisical FPGA, respectively.
