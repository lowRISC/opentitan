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
at it via the `PROV_EXTS_DIR` envar. This tells Bazel to instantiate a local
repo called `@provisioning_exts`.

## OTP Image Definitions

To define additional OTP configurations downstream, one must add OTP targets
to the `EXT_EARLGREY_OTP_CFGS` and `EXT_EARLGREY_SKUS` dictionaries in their
downstream `@provisioning_exts` Bazel repo.

## Personalization Firmware

The personalization firmware `ft_personalize.c` defines two `extern` C functions
that are invoked before and after certificates are endorsed off-device,
respectively:
`status_t personalize_extension_pre_cert_endorse(...)`
`status_t personalize_extension_post_cert_endorse(...)`

Additionally, the FT provisioning test harness provides an hook function to call
during the certificate endorsement operation:
`pub fn ft_ext(endorsed_cert_concat: ArrayVec<u8, 4096>) -> Result<ArrayVec<u8, 4096>>`

The default functions provided in this example external Bazel repo do nothing.
However, this provides a mechanism for SKU owners / customers to develop
closed-source personalization FW extensions, that can make use of open-source
code.

To configure a SKU to use downstream hooks, on must update their SKUs
configuration definition in the `EXT_EARLGREY_SKUS` dictionary in the
`@provisioning_exts` repo.
