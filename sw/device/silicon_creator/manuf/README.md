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

## Manufacturing Stages

The following section describes the EarlGrey manufacturing stages with respect
to the state of OTP. See `//hw/ip/otp_ctrl/data/earlgrey_a0_skus/sival/BUILD`
for more details.

### `MANUF_EMPTY`

The `MANUF_EMPTY` represents the initial state of OTP excluding the life cycle
partition.

### `MANUF_INITIALIZED`

In the `MANUF_INITIALIZED` state the SECRET0 partition is configured to enable
device transitions between `test_unlock` and `test_locked` states, as well as
to transition out of `test_unlock` into either `dev`, `prod`, or `prod_end`
state.

### `MANUF_INDIVIDUALIZED`

In the `MANUF_INDIVIDUALIZED` state the HW_CFG, CREATOR_SW and OWNER_SW OTP
partitions are configured. This state also includes the OTP configuration
performed in the `MANUF_INITIALIZED` state.

### `MANUF_PERSONALIZED`

The `MANUF_PERSONALIZED` OTP profile configures the SECRET1 and SECRET2
partitions. This state also includes the OTP configuration performed in the
`MANUF_INDIVIDUALIZED` state.

## OTP Partition versus Life Cycle Stages

Partition / Manuf | `EMPTY` | `INITIALIZED` | `INDIVIDUALIZED` | `PERSONALIZED`
:-----------------|:-------:|:-------------:|:----------------:|:--------------:
`HW_CFG`          |         |               | Y                | Y
`CREATOR_SW_CFG`  |         |               | Y                | Y
`OWNER_SW_CFG`    |         |               | Y                | Y
`SECRET0`         |         | Y             | Y                | Y
`SECRET1`         |         |               |                  | Y
`SECRET2`         |         |               |                  | Y

## Life Cycle versus Manufacturing Stages

Life Cycle / Manuf   | `EMPTY` | `INITIALIZED` | `INDIVIDUALIZED` | `PERSONALIZED`
:--------------------|:-------:|:-------------:|:----------------:|:--------------:
`RAW`                | Y       |               |                  |
`TEST_UNLOCKED0`     | Y       | Y             |                  |
`TEST_UNLOCKED{1-7}` |         | Y             | Y                |
`TEST_LOCKED{0-7}`   |         | Y             |                  |
`DEV`                |         |               | Y                | Y
`PROD`               |         |               | Y                | Y
`PROD_END`           |         |               | Y                | Y
`RMA`                |         |               | Y                | Y
