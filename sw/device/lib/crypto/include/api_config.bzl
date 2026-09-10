# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

CRYPTOLIB_API_CONFIG_HEADER = """\
// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_CRYPTOLIB_BUILD_CONFIG_H_
#define OPENTITAN_CRYPTOLIB_BUILD_CONFIG_H_

/**
 * @file
 * @brief Build configuration options for the OpenTitan cryptography library.
 *
 * Generated as part of an OpenTitan cryptography library build.
 *
 * It describes the configuration of the the library and must match the library
 * archive being linked. Specifically, it defines ABI-affecting configuration
 * selected when building the library. Consumers should not modify or define
 * these values manually.
 */
{cryptolib_defines}
#endif /* OPENTITAN_CRYPTOLIB_BUILD_CONFIG_H_ */
"""

def _cryptolib_api_config_header_impl(ctx):
    output_name = ctx.attr.name
    if not output_name.endswith(".h"):
        output_name = "{}.h".format(output_name)
    header = ctx.actions.declare_file(output_name)

    lines = []
    if ctx.attr.buffer_integrity_checks:
        lines += [
            "#ifdef OTCRYPTO_DISABLE_BUF_INTEGRITY_CHECKS",
            "#error \"This release has been built with buffer integrity checks, so these cannot be disabled.\"",
            "#endif /* OTCRYPTO_DISABLE_BUF_INTEGRITY_CHECKS */",
        ]
    else:
        lines.append("#define OTCRYPTO_DISABLE_BUF_INTEGRITY_CHECKS")
    defines = "\n{}\n".format("\n".join(lines)) if lines else ""

    content = CRYPTOLIB_API_CONFIG_HEADER.format(
        cryptolib_defines = defines,
    )
    ctx.actions.write(
        output = header,
        content = content,
    )

    return [DefaultInfo(files = depset([header]))]

cryptolib_api_config_header = rule(
    implementation = _cryptolib_api_config_header_impl,
    attrs = {
        "buffer_integrity_checks": attr.bool(default = True, doc = "Perform additional integrity checks of buffers, at some additional cost"),
    },
)
