# Manufacturing Firmware

## Implementation Guidelines

1. Implement test cases as stand-alone libraries in the `lib` folder.
2. Each manufacturing test should have a stand-alone functional test to enable
   test execution accross various targets (FPGA, DV, Silicon). All functional
   tests use the `*_functest.c` suffix.
3. Consider using baseline OTP images that reflect the status of the device
   before running the manufacturing test, aiming for reproduceability in
   silicon targets. See the `provisioning_functest` Bazel target as an example.
4. Avoid all use of assertions in manufacturing test cases. The test must be
   able to serialize the test result to the host. This enables the host to
   aggregate metrics across devices.

## Testplan

- [Test Plan](data/manuf_testplan.hjson)
