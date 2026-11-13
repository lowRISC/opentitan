# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("//rules:certificates.bzl", "certificate_template")

def uds_cert_libs(name, template, visibility = None):
    """Creates UDS certificate builder libraries for a given UDS template.

    The template's `name` field must be "uds" due to how the underlying
    certificate templating and code generation function.

    Args:
      name: prefix for the generated targets.
      template: the UDS certificate template HJSON.
      visibility: Visibility of the generated targets.

    This macro creates:
      - `<name>_uds_template`: the generated template.
      - `<name>_uds_template_library`: the generated template code.
      - `<name>_uds_template_unittest`: the generated template unit test.
      - `<name>_uds_cert_build`: An X.509 (ECDSA) UDS certificate builder lib.
      - `<name>_mldsa_uds_cert_build`: An ML-DSA UDS certificate builder lib.
    """
    template_name = "{}_uds_template".format(name)
    certificate_template(
        name = template_name,
        template = template,
        # The UDS builder sources from this prefix and hard-codes "uds" symbol names.
        out_basename = "uds",
        include_prefix = "sw/device/silicon_creator/lib/cert",
    )
    native.cc_library(
        name = "{}_uds_cert_build".format(name),
        srcs = [
            Label(":dice_uds_cert_build.c"),
        ],
        deps = [
            ":{}_library".format(template_name),
            Label(":cert"),
            Label(":dice_api"),
            Label(":template"),
            Label("//sw/device/lib/base:hardened"),
            Label("//sw/device/silicon_creator/lib:error"),
            Label("//sw/device/silicon_creator/lib/drivers:hmac"),
            Label("//sw/device/silicon_creator/lib/drivers:lifecycle"),
            Label("//sw/device/silicon_creator/lib/sigverify:ecdsa_p256_key"),
        ],
        # We don't want a SKU to silently end up with two UDS cert builders,
        # so we always link to ensure a link error in this case.
        alwayslink = True,
        visibility = visibility,
    )
    native.cc_library(
        name = "{}_mldsa_uds_cert_build".format(name),
        srcs = [
            Label(":dice_mldsa_uds_cert_build.c"),
        ],
        deps = [
            ":{}_library".format(template_name),
            Label(":cert"),
            Label(":dice_api"),
            Label(":dice_mldsa_api"),
            Label(":dice_mldsa_keys"),
            Label(":template"),
            Label("//sw/device/lib/base:hardened_memory"),
            Label("//sw/device/lib/base:memory"),
            Label("//sw/device/silicon_creator/lib/drivers:hmac"),
            Label("//sw/device/silicon_creator/lib/drivers:kmac"),
            Label("//sw/device/silicon_creator/lib/drivers:lifecycle"),
            Label("//sw/device/silicon_creator/lib/sigverify:mldsa_key"),
            Label("//third_party/embedpqc:mldsa44_tiny"),
            Label("//third_party/embedpqc:mldsa87_tiny"),
            Label("//third_party/embedpqc/ports:mldsa44_tiny_caller"),
            Label("//third_party/embedpqc/ports:mldsa87_tiny_caller"),
        ],
        # We don't want a SKU to silently end up with two UDS cert builders,
        # so we always link to ensure a link error in this case.
        alwayslink = True,
        visibility = visibility,
    )
