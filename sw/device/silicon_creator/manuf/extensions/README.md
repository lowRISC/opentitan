# Provisioning Flow Extensions

Provisioning an Earlgrey chip requires executing code on devivce during two core
phases:

1. Chip Probe (CP): when the wafer is still intact, and
2. Final Test (FT): when each chip has been packaged and loaded into a socket.
For the most part, the CP process is the same across all Earlgrey chips,
regardless of the SKU. However, the FT process can differ based on the target
SKU.

## FT Provisioning Overview

There are two main phases during FT provisioning:
1. individualization, and
2. personalization.

## Customizing FT Provisioning Flows

Various components of the reference FT provisioning flow can be extended to
satisfy the requirements of various SKUs. Specifically, there is Bazel
infrastructure, and example code, in place to demonstrate how one can define:
1. downstream OTP configurations for a custom SKU, and
2. downstream personalization firmware and host harness extensions for a custom SKU.

Defining both start by defining an additional Bazel repo location on your system
that resembles the directory this README.md is located in, and pointing Bazel
at it via using the following module override on the command line of Bazel:
```shell
# Here we capture the repeated override arg in an environment variable.
# You might want to consider using this in a .bazelrc file instead.
export BAZEL_OVERRIDE_ARGS=--override_module=ot_provisioning_exts=/path/to/repo

# Run some tests using the SKUs in the custom repository.
bazelisk test ${BAZEL_OVERRIDE_ARGS} --test_output=streamed //sw/host/provisioning/orchestrator/tests/...
```
This override tells Bazel to override the module called repo called `ot_provisioning_exts`.
This module provides two repositories `@provisioning_exts` and `@provisioning_exts_extra`.
See [`MODULE.bazel`](/MODULE.bazel) for more details.
See https://github.com/lowRISC/ot-sku for a non-trivial example.

## OTP Image Definitions

To define additional OTP configurations downstream, one must add OTP targets
to the `EXT_EARLGREY_OTP_CFGS` and `EXT_EARLGREY_SKUS` dictionaries in their
downstream `@provisioning_exts` Bazel repo.

## Execution Environments

To define additional execution environments downstream, add `exec_env`
compatible entries to the `EXT_EXEC_ENV_SILICON_ROM_EXT` dictionary in the
downstream `@provisioning_exts` Bazel repo.

## Personalization Firmware

The personalization firmware `ft_personalize.c` defines two `extern` C functions
that are invoked before and after certificates are endorsed off-device,
respectively:
`status_t personalize_extension_pre_cert_endorse(...)`
`status_t personalize_extension_post_cert_endorse(...)`

Additionally, the FT provisioning test harness provides an hook function to call
during the certificate endorsement operation:
`pub fn ft_ext(_response: &PersonalizeResponse) -> Result<Option<String>>`

The default functions provided in this example external Bazel repo do nothing.
However, this provides a mechanism for SKU owners / customers to develop
closed-source personalization FW extensions, that can make use of open-source
code.

To configure a SKU to use downstream hooks, on must update their SKUs
configuration definition in the `EXT_EARLGREY_SKUS` dictionary in the
`@provisioning_exts` repo.
