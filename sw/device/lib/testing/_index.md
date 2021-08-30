---
title: "Chip-Level Test Libraries"
---

This subtree provides libary code for writing chip-level tests.
Test library code should be considered any (reusable) code that could aid in the writing of chip-level tests.

## Test Types
- **Chip-level Tests** - A collection of software level tests that run on OpenTitan hardware, whose main purpose is pre-silicon verification and post-silicon bringup.
These tests consist of: smoke, IP integration, and system-level tests.
These tests are all executed on-device using the [on-device test framework]({{< relref "sw/device/lib/testing/test_framework/index.md" >}}).
While most of these tests are top-level agnostic, some are not.
  - **Smoke Tests** - A software level test, written in C using DIFs, that performs a minimal set of operations on a given IP block to verify that it is alive and functioning.
  - **IP Integration Tests** - A software level test, written in C, that exercises some specific functionality specific to a given IP and toplevel.
  The Eargrey toplevel [test plan](https://docs.opentitan.org/hw/top_earlgrey/doc/dv/#testplan) describes these tests.
  - **System-level Scenario Test** - A software level test, written in C, that mimics complex system level use case scenarios.
  Such a test is designed to encompass multiple pieces of functionality tested by the IP integration tests.

## Subfoldering Rules
- [on-device test framework]({{< relref "sw/device/lib/testing/test_framework/index.md" >}})
code will live in: **sw/device/lib/testing/test\_framework**.
- Remaining test library code will **_not_** be subfoldered.

## File Naming Conventions
- Test libary code will be named: **{IP or functionality name}_testutils.{h,c}**

## Documentation Index

{{% sectionContent %}}
