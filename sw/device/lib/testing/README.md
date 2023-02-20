---
title: "Chip-Level Test Libraries"
---

# Overview

This subtree contains _test library code_ that could aid in the writing of [chip-level tests]({{< relref "sw/device/tests/index.md" >}}).
Test library code consists of two components:
1. `testutils` libraries, and
2. the [on-device test framework]({{< relref "sw/device/lib/testing/test_framework/index.md" >}}).

Functions in `testutils` libraries are designed to wrap several DIF invocations that are commonly used together across many chip-level tests.
They are _not_ designed to wrap a single DIF call.

The [on-device test framework]({{< relref "sw/device/lib/testing/test_framework/index.md" >}}) provides a generic platform for writing chip-level tests.

# Style Guide

- All `testutils` libraries should be placed in `sw/device/lib/testing/*`
- The [on-device test framework]({{< relref "sw/device/lib/testing/test_framework/index.md" >}})
code will live in: `sw/device/lib/testing/test\_framework`.
- `testutils` libraries will be named: `<IP or functionality name>_testutils.<h,c>`
- All `testutils` function names should take on the following format: `<IP or functionality name>_testutils_<function name>()`.
  This corresponds to the format: `<filename>_<function name>()`.
- There is no strict return typing required, though ideally most `testutils` functions should return **void** or **bool**.
  This is because test errors should be checked in `testutils` functions themselves using the `CHECK()` macros defined in `sw/device/lib/testing/check.h`.
  - Functions that return **bool** to represent an error should be marked with **OT_WARN_UNUSED_RESULT** to avoid mistakenly ignoring errors.
    Return **false** to represent an error.
- Try to keep `testutils` libraries toplevel agnostic (e.g., don’t include `hw/top_earlgrey/sw/autogen/top_earlgrey.h` if you can avoid it).
  This means `dif_<ip>_init()` DIFs should be invoked in chip-level tests, *not* `testutils`, and the DIF handles should be passed in as parameters to `testutils` functions.
- Pass-through `sw/device/lib/dif_base.h` types where appropriate.
  This allows testutils functions to easily mix with DIFs within chip-level tests.
- Avoid defining testutils that call a single DIF, and use the DIF directly.
  If a DIF does not exist for your needs, create one by following the [DIF development guide]({{< relref "sw/device/lib/dif" >}}).

{{% sectionContent %}}
