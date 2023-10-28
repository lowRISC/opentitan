# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

def splice_bitstream(ctx, env, name, bitstream, mmis, datas, gen_vivado_image, opentitantool, splice_tool):
    """Splice a bitstream.

    Args:
      name: The name of the rule/basename of the output file.
      bitstream: The input bitstream file.
      mmis: The MMI meminfo files.
      datas: The data to splice into the bitstream.
      gen_vivado_image: The gen_vivado_image script.
      opentitantool: Opentitantool binary
    """
    output = ctx.actions.declare_file("{}.bit".format(name))

    args = ctx.actions.args()
    args.add("--gen_vivado_image", gen_vivado_image.executable)
    args.add("--opentitantool", opentitantool.executable)
    args.add_joined("--mmi", mmis, join_with = ",")
    args.add_joined("--data", datas, join_with = ",")
    args.add("--output", output)
    args.add(bitstream)

    ctx.actions.run(
        mnemonic = "Splice",
        outputs = [output],
        inputs = [bitstream] + mmis + datas,
        arguments = [args],
        execution_requirements = {
            "no-sandbox": "",
        },
        tools = [gen_vivado_image, opentitantool],
        executable = splice_tool,
        env = env,
    )

    return output
