# IMM_ROM_EXT Prebuilts

This markdown explains all of the prebuilt collections in this folder and the
usage of them.

## NOP IMM_ROM_EXT

* The `nop.o` is built by the following command:
  `riscv32-unknown-elf-as -march=rv32i nop.S -o nop.o`
* This `IMM_ROM_EXT` only contains a section called `.rom_ext_immutable` and a
  single `ret` command, and it is only used for testing.
