hw/ip/otbn/util/otbn_as.py -o otbn_test/p256_proj_add_test.o sw/otbn/crypto/tests/bazel query 'tests(//sw/device/lib/dif:all)'.s
hw/ip/otbn/util/otbn_ld.py -o otbn_test/p256_proj_add_test.elf otbn_test/p256_proj_add_test.o
hw/ip/otbn/dv/otbnsim/standalone.py otbn_test/p256_proj_add_test.elf -v