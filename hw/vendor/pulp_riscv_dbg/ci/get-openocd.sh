#!/usr/bin/env bash

set -e

VERSION="af3a034b57279d2a400d87e7508c9a92254ec165"

mkdir -p $RISCV/
cd $RISCV

check_version() {
    $1 --version | awk "NR==1 {if (\$NF>$2) {exit 0} exit 1}" || (
	echo $3 requires at least version $2 of $1. Aborting.
	exit 1
    )
}


if [ -z ${NUM_JOBS} ]; then
    NUM_JOBS=1
fi

if ! [ -e $RISCV/bin/openocd ]; then
    if ! [ -e $RISCV/riscv-openocd ]; then
	git clone https://github.com/riscv/riscv-openocd.git
    fi
    check_version automake 1.14 "OpenOCD build"
    check_version autoconf 2.64 "OpenOCD build"

    cd riscv-openocd
    git checkout $VERSION
    git submodule update --init --recursive

    echo "Compiling OpenOCD"
    ./bootstrap
    ./configure --prefix=$RISCV --disable-werror --disable-wextra --enable-remote-bitbang
    make -j${NUM_JOBS}
    make install
    echo "Compilation Finished"
fi

