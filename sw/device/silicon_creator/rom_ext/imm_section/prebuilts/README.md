# ROM_EXT IMM_SECTION Prebuilts

This markdown explains all of the prebuilt collections in this folder and the
usage of them.

## NOP IMM_SECTION

* The `nop.o` is built by the following command:
  `riscv32-unknown-elf-as -march=rv32i nop.S -o nop.o`
* This `IMM_SECTION` only contains a section called `.rom_ext_immutable` and a
  single `ret` command, and it is only used for testing.
