---
title: "On-Device Test Framework"
---

![Chip-level Test Infrastructure](chip_level_test_infra.svg)

Currently, chip-level tests are executed across three targets (DV, Verilator, and FPGA), using host-side test initiation tools, and an on-device test framework, as shown in the figure above.
On the _host_ side, two main tools are used to initiate tests on the device. For the DV simulation target, the [dvsim.py](https://cs.opensource.google/opentitan/opentitan/+/master:util/dvsim/) tool is used, while for Verilator and FPGA targets, the [systemtest (pytest)](https://cs.opensource.google/opentitan/opentitan/+/master:test/systemtest/) tool is used.
Focusing on the _device_ side, for all three targets, the [on-device test framework](https://cs.opensource.google/opentitan/opentitan/+/master:sw/device/lib/testing/test_framework/test_main.c) is used to provide a uniform execution environment for chip-level tests.
The [on-device test framework](https://cs.opensource.google/opentitan/opentitan/+/master:sw/device/lib/testing/test_framework/test_main.c) provides boilerplate setup code that configures the UART for communicating messages and test results back to the host.
To write a chip-level test that uses this framework, one must create a new C file for the test with the following boilerplate code:

```
#include "sw/device/lib/testing/test_framework/test_main.h"
#include "sw/device/lib/testing/check_.h" // if calls to CHECK() are made
#include "sw/device/lib/runtime/log.h"  // if calls to LOG_INFO() are made

const test_config_t kTestConfig;

bool test_main() {
  // Test program entry point.
  return true;
}
```

Check out the [rv\_timer smoke test](https://cs.opensource.google/opentitan/opentitan/+/master:sw/device/tests/rv_timer_smoketest.c) for an example chip-level test that uses the current test framework.
