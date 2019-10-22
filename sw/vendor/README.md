# Work with software code in external repositories

Please refer to [vendor_hw](../../doc/vendor_hw.md) for more details on
rationale of vendoring external repositories.


## RISC-V Compliance Suite

The RISC-V Compliance Suite defines a series of tests that to ensure the
RISC-V system is complies with the RISC-V specification.  Normally such a test
would be run at the core level instead of the system level, but doing so confers
advantages to ensure system integration did not alter the original properties
of the core (for example breaking byte or half-word accesses).

To vendor in RISC-V Compliance Suite, please use the commands below.
```
./util/vendor_hw.py sw/vendor/riscv_compliance.vendor.hjson --verbose
```
