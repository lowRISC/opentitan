# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

def _orchestrator_cw340_settings_impl(settings, attr):
    return {
        "//sw/host/provisioning/orchestrator/src:env": "//hw/top_earlgrey:fpga_cw340_rom_with_fake_keys",
        "//sw/host/provisioning/orchestrator/src:otp": "//hw/top_earlgrey/data/otp/emulation:otp_img_test_unlocked0_manuf_empty",
    }

_orchestrator_cw340_settings = transition(
    implementation = _orchestrator_cw340_settings_impl,
    inputs = [],
    outputs = [
        "//sw/host/provisioning/orchestrator/src:env",
        "//sw/host/provisioning/orchestrator/src:otp",
    ],
)

def _orchestrator_test_settings_transition_impl(ctx):
    info = ctx.attr.target[DefaultInfo]
    return [
        DefaultInfo(
            files = info.files,
            data_runfiles = info.data_runfiles,
        ),
    ]

orchestrator_cw340_test_settings_transition = rule(
    implementation = _orchestrator_test_settings_transition_impl,
    cfg = _orchestrator_cw340_settings,
    attrs = {
        "target": attr.label(),
        "_allowlist_function_transition": attr.label(
            default = "@bazel_tools//tools/allowlists/function_transition_allowlist",
        ),
    },
)
