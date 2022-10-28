#!/bin/bash
_GET_OBJS=$(find ./out/run -type f -iregex '.*test\.o')
if [[ -z "${RISCV_TOOLCHAIN}" ]]; then
   echo "Please define RISCV_TOOLCHAIN to have access to objdump."
   exit 1
fi
for obj in $_GET_OBJS; do
    "$RISCV_TOOLCHAIN"/bin/riscv32-unknown-elf-objdump -d "$obj" > "$(dirname "$obj")"/test.dump
done
