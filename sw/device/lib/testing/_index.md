---
title: "Chip-Level Test Libraries"
---

# Overview

This subtree contains _test libary code_ that could aid in the writing of [chip-level tests]({{< relref "sw/device/tests/index.md" >}}).

# Organization and Style Guide

## File Naming Conventions
- Test libary code will be named: **{IP or functionality name}_testutils.{h,c}**

## Subfoldering Rules
- [on-device test framework]({{< relref "sw/device/lib/testing/test_framework/index.md" >}})
code will live in: **sw/device/lib/testing/test\_framework**.
- Remaining test library code will **_not_** be subfoldered.

# Documentation Index

{{% sectionContent %}}
