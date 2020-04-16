# RISC-V Compliance Task Group

This is a repository for the work of the RISC-V Foundation Compliance Task Group. The repository owners are:
- Jeremy Bennett (Embecosm)
- Lee Moore (Imperas)

Details of the RISC-V Foundation, the work of its task groups, and how to become a member can be found at [riscv.org](https://riscv.org/).

## Contribution process

You are encouraged to contribute to this repository by submitting pull requests and by commenting on pull requests submitted by other people.

- Where a pull request is non-controversial one of the repository owners will immediately merge it. The repository uses rebase merges to maintain a linear history.

- Other pull requests will be publicised to the task group for comment and decision at a subsequent meeting of the group. Everyone is encouraged to comment on a pull request. Such pull requests will be merged by when a consensus/decision has been reached by the task group.

## Licensing

In general:
- code is licensed under the BSD 3-clause license (SPDX license identifier `BSD-3-Clause`); while
- documentation is licensed under the Creative Commons Attribution 4.0 International license (SPDX license identifier `CC-BY-4.0`).

The files [`COPYING.BSD`](./COPYING.BSD) and [`COPYING.CC`](./COPYING.CC) in the top level directory contain the complete text of these licenses.

## Engineering practice

- Documentation uses the structured text format _AsciiDoc_.  See [`doc/README.adoc`](doc/README.adoc) for more details.

- Some directories use `ChangeLog` files to track changes in the code and documentation.  Please honor these, keeping them up to date and including the ChangeLog entry in the _git_ commit message.

- Please include a comment with the SPDX license identifier in all source files, for example:
```
// SPDX-License-Identifier: BSD-3-Clause
```

## Running the compliance tests

The only setup required is to define where the toolchain is found, and where the target / device is found.

For the toolchain, the binaries must be in the search path and the compiler prefix is defined on the make line. The default value for this is

    RISCV_PREFIX ?= riscv64-unknown-elf-

The path to the RUN_TARGET is defined within the riscv-target Makefile.include.

To run the rv32i test suite on riscvOVPsim

    make RISCV_TARGET=riscvOVPsim RISCV_DEVICE=rv32i

### Accessing riscvOVPsim

As we create the RISCV.org compliance test suite, the Imperas developed _riscvOVPsim_ compliance simulator is included as part of this GitHub repository. For more information please contact info@ovpworld.org or info@imperas.com.

For more information on riscvOVPsim look here: [riscv-ovpsim/README.md](riscv-ovpsim/README.md) and here: [riscv-ovpsim/doc/riscvOVPsim_User_Guide.pdf](riscv-ovpsim/doc/riscvOVPsim_User_Guide.pdf).

### Using the simulators from the Sail RISC-V formal model

The [Sail RISC-V formal model](https://github.com/rems-project/sail-riscv) generates two
simulators, in C and OCaml.  They can be used as test targets for this compliance suite.

For this purpose, the Sail model needs to be checked out and built on
the machine running the compliance suite.  Follow the build
instructions described the README for building the RV32 and RV64
models.  Once built, please add `$SAIL_RISCV/c_emulator` and
`$SAIL_RISCV/ocaml_emulator` to your path, where $SAIL_RISCV is the
top-level directory containing the model.

To test the compliance of the C simulator for the current RV32 and RV64 tests, use

    make RISCV_TARGET=sail-riscv-c all_variant

while the corresponding command for the OCaml simulator is

    make RISCV_TARGET=sail-riscv-ocaml all_variant

### Using the GRIFT simulator

The [GRIFT](https://github.com/GaloisInc/grift) formal model and simulation tool
can be used as a test target for this compliance suite.

GRIFT needs to be cloned and built on the machine running the compliance
suite. Follow the build instructions described in the README for building the
GRIFT simulator. Once build, add the generated `grift-sim` executable to your
path.

To test the compliance of the GRIFT simulator for the current RV32 and RV64
tests, use

    make RISCV_TARGET=grift all_variant

Note that the I-MISALIGN_LDST test fails for GRIFT because GRIFT currently
supports misaligned loads and stores in hardware, while the test is specifically
written for systems that trap on misaligned loads and stores.
