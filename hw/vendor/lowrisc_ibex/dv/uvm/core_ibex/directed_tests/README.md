# Directed Tests

This directory contains the custom directed tests as well as scripts and headers for running directed tests vendored from various open source repositories.

Currently following open source test suites are vendored:
- [riscv-tests](https://github.com/riscv-software-src/riscv-tests)
- [riscv-arch-tests](https://github.com/riscv-non-isa/riscv-arch-test)
- epmp-tests ([fork](https://github.com/lowRISC/riscv-isa-sim/tree/mseccfg_tests) from an opensource [repo](https://github.com/joxie/riscv-isa-sim))

## Generating test list

To generate a testlist containing all of the directed tests (custom + tests from vendored repos).

```
python3 gen_testlist.py --add_tests riscv-tests,riscv-arch-tests,epmp-tests
```

Please note that the custom directed tests needs to be added in the `gen_testlist.py` script and it needs to be run in order to update `directed_testlist.yaml`.
