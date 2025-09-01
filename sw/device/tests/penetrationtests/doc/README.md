# Penetration Testing Framework

The purpose of this framework is to perform side-channel analysis (SCA) and fault injection (FI) attacks on the FPGA as well as on the chip.

![Full hardware setup](pentest_setup.png)

As shown in the block diagram, the pentest framework runs on the target and receives configuration commands by the SCA and FI [ot-sca](https://github.com/lowRISC/ot-sca) framework.

## Usage

To run the penetration tests either on the FPGA or the chip, please follow the instructions in the [ot-sca](https://github.com/lowRISC/ot-sca) repository.
You can also find the files to communicate to the pentest framework via Python scripts in //sw/host/penetrationtests/python.

## Contributing

When contributing to the pentest framework, run the automated testing as explained below.

### Building Images

Due to code size memory limitations, the firmware for the chip and the FPGA is split into a SCA, general FI, IBEX FI, and OTBN FI binary. To build these binaries for the chip, run:
```console
cd $REPO_TOP
./bazelisk.sh build \
  --//signing:token=//signing/tokens:cloud_kms_sival \
  //sw/device/tests/penetrationtests/firmware:pen_test_sca_silicon_owner_sival_rom_ext

./bazelisk.sh build \
  --//signing:token=//signing/tokens:cloud_kms_sival \
  //sw/device/tests/penetrationtests/firmware:pen_test_fi_silicon_owner_sival_rom_ext

./bazelisk.sh build \
  --//signing:token=//signing/tokens:cloud_kms_sival \
  //sw/device/tests/penetrationtests/firmware:pen_test_fi_ibex_silicon_owner_sival_rom_ext

./bazelisk.sh build \
  --//signing:token=//signing/tokens:cloud_kms_sival \
  //sw/device/tests/penetrationtests/firmware:pen_test_fi_otbn_silicon_owner_sival_rom_ext

./bazelisk.sh build \
  --//signing:token=//signing/tokens:cloud_kms_sival \
  //sw/device/tests/penetrationtests/firmware:pen_test_cryptolib_sym_fi_silicon_owner_sival_rom_ext

./bazelisk.sh build \
  --//signing:token=//signing/tokens:cloud_kms_sival \
  //sw/device/tests/penetrationtests/firmware:pen_test_cryptolib_asym_fi_silicon_owner_sival_rom_ext

./bazelisk.sh build \
  --//signing:token=//signing/tokens:cloud_kms_sival \
  //sw/device/tests/penetrationtests/firmware:pen_test_cryptolib_sym_sca_silicon_owner_sival_rom_ext

./bazelisk.sh build \
  --//signing:token=//signing/tokens:cloud_kms_sival \
  //sw/device/tests/penetrationtests/firmware:pen_test_cryptolib_asym_sca_silicon_owner_sival_rom_ext
```

The binaries are located in `bazel-bin/sw/device/tests/penetrationtests/firmware/`.

## Automated Testing

To automatically test whether the pentest framework works, an automatic testing framework is provided.
This framework compares the responses of the pentest frameworks with reference testvectors.

Use the following command to automatically test the Ibex FI tests on the CW340 FPGA board:

```console
cd $REPO_TOP
./bazelisk.sh run //sw/device/tests/penetrationtests:fi_ibex_fpga_cw340_sival_rom_ext
```

In addition, we have Python scripts to use the pentest framework in //sw/host/penetrationtests/python.
These scripts are also tested.
Use the following command to automatically test the Ibex FI tests on the CW340 FPGA board:

```console
cd $REPO_TOP
./bazelisk.sh run //sw/device/tests/penetrationtests:fi_ibex_python_test_fpga_cw340_sival_rom_ext
```
