#!/bin/bash
# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

set -e

if [ "$#" -ne 2 ]; then
  echo "Basic script to build a binary from a single OTBN assembly file. Input file is"
  echo "first argument, prefix for output files is second argument. Only use .data and"
  echo ".text sections in input asm"
  echo ""
  echo "$0 input.S out_dir/prog"
  echo ""
  echo "Will produce:"
  echo ""
  echo "* out_dir/prog.o - input.S assembled object file"
  echo "* out_dir/prog.elf - Linked binary"
  echo "* out_dir/prog.dis - Disassembled binary"
  echo "* out_dir/prog_imem.elf - .text section alone"
  echo "* out_dir/prog_dmem.elf - .data section alone"
  exit 1
fi

SCRIPT_FILE=$(readlink -f "$BASH_SOURCE")
OTBN_UTIL_DIR=$(dirname "$SCRIPT_FILE")

$OTBN_UTIL_DIR/otbn-as $1 -o $2.o
$OTBN_UTIL_DIR/otbn-ld $2.o -o $2.elf
$OTBN_UTIL_DIR/otbn-objdump -fhSD $2.elf > $2.dis
riscv32-unknown-elf-objcopy -j .text $2.elf $2_imem.elf
riscv32-unknown-elf-objcopy -j .data $2.elf $2_dmem.elf
