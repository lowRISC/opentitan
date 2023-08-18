# ROM

The ROM is the first boot stage in the Reference Secure Boot implementation, and starts executing at device reset.
The ROM is programmed into the chip's ROM during wafer manufacturing, and cannot be changed.
The ROM needs to prepare the OpenTitan chip for executing a ROM_EXT, including ensuring the loaded ROM_EXT is allowed to be executed on this chip.

# References

- [Secure Boot Specification](../../../../doc/security/specs/secure_boot/README.md)
- [Mask ROM Specification](doc/rom_overview_specification.md)
- [Manifest Format](../rom_ext/doc/manifest.md)
- [Signing Keys](keys/README.md)
- [Signature Verification](doc/sigverify.md)
- [ROM End-End Regression Setup](doc/e2e_tests.md)
- [Test Plan](data/rom_e2e_testplan.hjson)
