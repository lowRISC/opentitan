#!/bin/bash
export PATH=/usr/pack/pulpsdk-1.0-kgf/artifactory/pulp-sdk-release/pkg/pulp_riscv_gcc/1.0.16/bin/riscv32-unknown-elf:$PATH
export PATH=/usr/pack/riscv-1.0-kgf/riscv64-gcc-11.2.0/bin:$PATH
export RISCV=/usr/pack/riscv-1.0-kgf/riscv64-gcc-11.2.0
export PATH=/usr/pack/pulpsdk-1.0-kgf/artifactory/pulp-sdk-release/pkg/pulp_riscv_gcc/1.0.16/bin:$PATH
export QUESTASIM_HOME=/usr/pack/questa-2022.3-bt/questasim/

ulimit -n 2048

git submodule update --init --recursive
