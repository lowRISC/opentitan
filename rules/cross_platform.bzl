# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

"""Rules for defining cross-platform libraries."""

def dual_inputs(shared = [], device = [], host = []):
    """Constructs a cross-platform input for use with dual_cc_library."""
    return struct(shared = shared, device = device, host = host)

def dual_cc_device_library_of(label):
    """
    Given the label of a dual_cc_library, returns the label for the
    on-device library. This library is private to the Bazel package that
    defines it.
    """
    return "{}_on_device_do_not_use_directly".format(label)

def dual_cc_library(
        name,
        on_device_config_setting = "//rules:opentitan_platform",
        srcs = [],
        hdrs = [],
        deps = [],
        **kwargs):
    """
    Defines a cc_library whose contents are dependent on whether it is
    depended on in an on-device or on-host setting.

    The macro takes the same arguments as cc_library, but has special
    behavior for `hdrs`, `srcs`, and `deps`, which may either be a list of
    labels that would usually be inputs to a cc_library, or a dual_inputs object.
    The later case allows inputs to be designated as being shared, on-device-only,
    or off-device-only.

    This rule only needs to be used when the sources for on-device are different
    from on-host, such as for mockable interfaces. In this case, the on-device
    library may still be used on-host via `dual_cc_device_library_of`, and it will
    use the host-side versions of its dependencies. This is useful for testing
    the on-device version using mocked dependencies.

    Args:
      @param name: The name of this rule.
      @param on_device_config_setting: A config_setting rule for determining what
             "on device" means.
      @param srcs: `cc_library()` sources; may be a list or a `dual_inputs()`.
      @param hdrs: `cc_library()` headers; may be a list or a `dual_inputs()`.
      @param deps: `cc_library()` dependencies; may be a list or a `dual_inputs()`.
      @param **kwargs: Arguments to forward to each `cc_library()`.

    Emits rules:
      cc_library    named: dual_cc_device_library_of(<name>)
      cc_library    named: <unspecified>  # Host-only library.
      alias         named: <name>
    """

    hdrs = hdrs if type(hdrs) != "list" else dual_inputs(shared = hdrs)
    srcs = srcs if type(srcs) != "list" else dual_inputs(shared = srcs)
    deps = deps if type(deps) != "list" else dual_inputs(shared = deps)

    native.cc_library(
        name = dual_cc_device_library_of(name),
        hdrs = hdrs.shared + hdrs.device,
        srcs = srcs.shared + srcs.device,
        deps = deps.shared + deps.device,
        visibility = ["//visibility:private"],
        **kwargs
    )

    off_device_name = "{}_on_host_do_not_use_directly".format(name)
    native.cc_library(
        name = off_device_name,
        hdrs = hdrs.shared + hdrs.host,
        srcs = srcs.shared + srcs.host,
        deps = deps.shared + deps.host,
        visibility = ["//visibility:private"],
        **kwargs
    )

    native.alias(
        name = name,
        actual = select({
            on_device_config_setting: dual_cc_device_library_of(name),
            "//conditions:default": off_device_name,
        }),
    )
