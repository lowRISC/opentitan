# Manufacturer Test Hooks - OTTF Feature

## Overview
The OpenTitan Test Framework (OTTF) defines both pre- and post-test hook
functions (see the prototypes below) that are invoked before and after
(respectively) a test runs. By default, these hook functions do nothing.
However, they provide a mechanism for manufacturers to develop closed-source
test initialization / cleanup code that can be used with open-source tests.

```c
bool manufacturer_pre_test_hook(void);
bool manufacturer_post_test_hook(void);
```

This feature is implemented with the help of some custom Bazel repository rules.
Specifically, in `sw/device/test/closed_source` we define a secondary Bazel
repository (`@manufacturer_test_hooks`) that is designed to be used in
conjunction with the main OpenTitan Bazel repository. Within this repository, we
define a `test_hooks` library that is linked with the OTTF. However, the
`test_hooks` library provided in this repository is merely an example, as the
test hook functions implemented do nothing, except `return true;`. Specifically,
running `bazel test //sw/device/tests:<target>` will run the test with the
default test hooks defined in `sw/device/tests/closed_source/test_hooks.c`.

## Implementing your own Test Hooks
If you are a manufacturer, and would like to implement custom test hooks (that
replace the defaults) you may do so by:

1. copying the `sw/device/tests/closed_source/` directory to another location on your system,
1. changing the implementation of the test hooks functions in `test_hooks.c`, and
1. invoking bazel with the `MANUFACTURER_HOOKS_DIR` environment variable set, e.g.,
   `MANUFACTURER_HOOKS_DIR=</path/to/test_hooks/> bazel test //sw/device/tests:<target>`

Note, you may do the above for multiple sets of test hooks if you so desire.
