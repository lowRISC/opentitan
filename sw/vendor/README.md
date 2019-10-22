# Work with software code in external repositories

Please refer to [vendor_hw](../../doc/vendor_hw.md) for more details on rationale of vendoring external repositories


## RISCV_COMPLIANCE

RISCV_COMPLIANCE defines a series of tests that to ensure the riscv core is compliant.
Normally such a test would be run at the core level instead of the system level, but doing so confers advantages to ensure system integration did not alter the original properties of the core (for example breaking byte or half-word accesses)

To vendor in riscv compliance, please use teh commands below
```
./util/vendor_hw.py sw/vendor/riscv_compliance.vendor.hjson --verbose
```
