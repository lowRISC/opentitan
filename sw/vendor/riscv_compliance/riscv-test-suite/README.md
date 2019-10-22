# RISC-V Test Suites

Tests are grouped into different functional test suites targeting the different subsets of the full RISC-V specifications.  There will be ISA and privilege suites.

For information on the test framework and other documentation on the compliance tests look at : [../doc/README.adoc](../doc/README.adoc) 

Currently there are twelve test suites checked into this repository. 

If you are looking to check compliance of RV32I in user mode then run the suites: RV32I and RV32UI

Test suites status:

Pretty Solid:
* RV32I (originally developed by Codasip, assertions and debug macros added by Imperas)
    * 55 focused tests, using the correct style/macros, excellent coverage of most instructions
    * no coverage of fence, scall, sbreak, pseudo and csr instructions
* RV32IM (developed by Imperas)
    * 7 focused tests, using the correct style/macros, excellent coverage
* RV32IMC (developed by Imperas)
    * 24 focused tests, using the correct style/macros
* RV64I (developed by Imperas)
    * 8 focused tests, using the correct style/macros
* RV64IM (developed by Imperas)
    * 3 focused tests, using the correct style/macros

Work in progress (user mode):
* RV32UI (from github/riscv-tests with poor coverage. Ported by Imperas)
    * 39 tests, uses original style, user mode, Imperas added signature
* RV32UA (from github/riscv-tests with poor coverage. Ported by Imperas)
    * 10 tests, uses original style, user mode, Imperas added signature
* RV32UC (from github/riscv-tests with poor coverage. Ported by Imperas)
    * 1 test, uses original style, user mode, Imperas added signature
* RV32UF (from github/riscv-tests with poor coverage. Ported by Imperas)
    * 11 tests, uses original style, user mode, Imperas added signature
* RV32UD (from github/riscv-tests with poor coverage. Ported by Imperas)
    * 10 tests, uses original style, user mode, Imperas added signature

Work in progress (starting on privilege modes):
* RV32SI (from github/riscv-tests with poor coverage. Ported by Imperas)
    * 6 tests, uses original style, Imperas added signature
* RV32MI (from github/riscv-tests with poor coverage. Ported by Imperas)
    * 8 tests, uses original style, Imperas added signature

To be worked on:
* RV64C
* RV32A
* RV64A
* RV64F
* RV64D
* RV32E
* RV32EC
* RV32EA
* RV32EF
* RV32ED