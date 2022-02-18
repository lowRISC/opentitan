Pointing to contents of meson-riscv32-unknown-elf-clang as a starting point

This is how it looks when installed in my system (comments are mine)
```
[binaries]
c = '/tools/riscv/bin/riscv32-unknown-elf-clang'

# Meson uses the following to point to clang++ so in bazel we'll refer to this
# as c++ or gcc
cpp = '/tools/riscv/bin/riscv32-unknown-elf-clang++'

ar = '/tools/riscv/bin/riscv32-unknown-elf-ar'
ld = '/tools/riscv/bin/riscv32-unknown-elf-ld'
c_ld = '/tools/riscv/bin/riscv32-unknown-elf-ld'
cpp_ld = '/tools/riscv/bin/riscv32-unknown-elf-ld'
objdump = '/tools/riscv/bin/riscv32-unknown-elf-objdump'
objcopy = '/tools/riscv/bin/riscv32-unknown-elf-objcopy'
strip = '/tools/riscv/bin/riscv32-unknown-elf-strip'
as = '/tools/riscv/bin/riscv32-unknown-elf-as'
```
