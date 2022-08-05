# DV for the ibex core

For detailed documention on how Ibex's verification works, please have a look at [the dedicated documentation page](https://ibex-core.readthedocs.io/en/latest/03_reference/verification.html).
This README provides a quick start guide to get things running.

## Prerequisites
You need to have Xcelium available on your machine.
You can check whether you have it available by running: `xrun --verison`

You also need Spike to be able to compare to in the cosimulation.
We use a lowRISC specific Spike which you can find [on its own GitHub page](https://github.com/lowRISC/riscv-isa-sim/tree/ibex_cosim).
Some quick build instructions from within the `riscv-isa-sim` repo:
```bash
mkdir build
cd build
../configure --enable-commitlog --enable-misaligned --prefix=$SPIKE_INSTALL_DIR
make
make install
export SPIKE_PATH=$SPIKE_INSTALL_DIR/bin
export PKG_CONFIG_PATH=$PKG_CONFIG_PATH:$SPIKE_INSTALL_DIR/lib/pkgconfig
```

You will need the [RISC-V toolchain](https://github.com/riscv-collab/riscv-gnu-toolchain).
You'll need to add this to your path and then also set the following environment variables:
```bash
export RISCV_GCC=riscv32-unknown-elf-gcc
export RISCV_OBJCOPY=riscv32-unknown-elf-objcopy
```

## Running tests

To run tests you can make variations of the following command, where you replace `$TEST_NAME` with the test (or a series of comma-separated tests) that you would like to run as specified in `dv/uvm/core_ibex/riscv_dv_extension/testlist.yaml`:
```bash
make --keep-going IBEX_CONFIG=opentitan SIMULATOR=xlm ISS=spike ITERATIONS=1 SEED=1 TEST=$TEST_NAME WAVES=0 COV=0
```