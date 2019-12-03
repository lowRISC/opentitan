# Building CoreMark

To build CoreMark under meson:

```sh
cd "${REPO_TOP}"
./meson_init.sh
ninja -C build-out/sw/${TARGET} sw/device/benchmarks/coremark/coremark_export
```

Where ${TARGET} is one of 'sim-verilator' or 'fpga'

This will give you a .bin and .elf file (suitable for either spiflash or
giving directly to `--meminit` for Verilator) which can be found in
`build-bin/sw/device/fpga/benchmarks/coremark`

# CoreMark Options

The meson build script alters ITERATIONS (specifying how many iterations
CoreMark does) depending on whether it is a sim-verilator or an fpga build. 1
iteration is used for sim-verilator, 100 for fpga.

The meson script is hardcoded to give PERFORMANCE_RUN with
TOTAL_DATA_SIZE=2000. These are settings required for reportable CoreMark
figures. If you wish to use other options please alter
`sw/device/benchmarks/coremark/meson.build` appropriately. See the CoreMark
README in `sw/vendor/eembc_coremark/README.md` for further information on the
possibilities.
