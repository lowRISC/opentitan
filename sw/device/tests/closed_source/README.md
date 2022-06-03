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
define a single `test_hooks` library that is linked with the OTTF. The
`test_hooks` library itself just contains default weak symbols for each test
hook function. However, the `test_hooks` library is linked with other libraries
based on a Bazel `config_setting` that allows you to toggle which test hook
library should be override the defaults. However, the Bazel `config_setting`s
and example manufacturer test hooks library (`test_hooks_1`) provided in this
repository are merely examples, as the test hook functions implemented do
nothing, except print a message and `return true;`.

To learn how to use the example default and non-default test hooks with existing
(open-source) tests, see the `sw/default/tests/closed_source/BUILD.bazel` file.

## Implementing your own Test Hooks
If you are a manufacturer, and would like to implement custom test hooks (that
replace the defaults) you may do so by:

1. copying the `sw/device/tests/closed_source/` directory to another location on
   your system,
1. follow the steps (labeled `TH-Step *`) in the
   `sw/default/tests/closed_source/BUILD.bazel` file to add additional test
   hook libraries / config settings,
1. invoking bazel with the `MANUFACTURER_HOOKS_DIR` environment variable set,
   and the proper `config_setting` , e.g.,
   `MANUFACTURER_HOOKS_DIR=</path/to/test_hooks/> bazel test
      //sw/device/tests:<target>
      --define test_hooks=<test hooks setting>`

Note, with the above configuration you may place several test hook libraries in
the same `MANUFACTURER_HOOKS_DIR`.

## Implementing your own Tests
If you are a manufacturer, and would like to implement custom (closed-source)
tests, you may do so by following the single step (labeled `OTFT-Step 1`) in the
`sw/default/tests/closed_source/BUILD.bazel` file.
