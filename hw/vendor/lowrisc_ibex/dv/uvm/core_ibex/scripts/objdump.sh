_GET_OBJS=$(find ./out/run -type f -iregex '.*test\.o')
for obj in $_GET_OBJS; do
    $RISCV_TOOLCHAIN/bin/riscv32-unknown-elf-objdump -d $obj > $(dirname $obj)/test.dump
done
