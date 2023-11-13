hw/ip/otbn/util/otbn_as.py -o p256_base_mult_test.o sw/otbn/crypto/tests/p256_base_mult_test.s
hw/ip/otbn/util/otbn_ld.py -o p256_base_mult_test.elf p256_base_mult_test.o
hw/ip/otbn/dv/otbnsim/standalone.py p256_base_mult_test.elf -v