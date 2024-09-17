# Penetration Testing Framework

The penetration testing framework is based on the [Cryptotest](../crypto/cryptotest/README.md) framework.
The purpose of this framework is to perform side-channel analysis (SCA) and fault injection (FI) attacks on the FPGA as well as on the chip.

To build the penetration testing framework for the ChipWhisperer CW310 FPGA board, run:
```console
cd $REPO_TOP
./bazelisk.sh build //sw/device/tests/penetrationtests/firmware:firmware_fpga_cw310_test_rom
```

Due to code size memory limitations, the firmware for the chip is split into a SCA and a FI binary. To build these binaries, run:
```console
cd $REPO_TOP
./bazelisk.sh build \
  --//signing:token=//signing/tokens:cloud_kms_sival \
  //sw/device/tests/penetrationtests/firmware:chip_pen_test_sca_silicon_owner_sival_rom_ext

./bazelisk.sh build \
  --//signing:token=//signing/tokens:cloud_kms_sival \
  //sw/device/tests/penetrationtests/firmware:chip_pen_test_fi_silicon_owner_sival_rom_ext
```

The binaries are located in `bazel-bin/sw/device/tests/penetrationtests/firmware/`.

To run the penetration tests either on the FPGA or the chip, please follow the instructions in the [ot-sca](https://github.com/lowRISC/ot-sca) repository.
