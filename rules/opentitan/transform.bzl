# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("@rules_cc//cc:find_cc_toolchain.bzl", "find_cc_toolchain")
load("@bazel_skylib//lib:paths.bzl", "paths")
load("@lowrisc_opentitan//rules/opentitan:util.bzl", "get_override")

def obj_transform(ctx, **kwargs):
    """Transform an object file via objcopy.

    Args:
      ctx: The context object for this rule.
      kwargs: Overrides of values normally retrived from the context object.
        output: The name of the output file.  Constructed from `name` and `suffix`
                 if not specified.
        src: The src File object.
        format: The objcopy output-format.
    Returns:
      The transformed File.
    """
    cc_toolchain = find_cc_toolchain(ctx).cc
    output = kwargs.get("output")
    if not output:
        name = get_override(ctx, "attr.name", kwargs)
        suffix = get_override(ctx, "attr.suffix", kwargs)
        output = "{}.{}".format(name, suffix)

    output = ctx.actions.declare_file(output)
    src = get_override(ctx, "attr.src", kwargs)
    out_format = get_override(ctx, "attr.format", kwargs)

    ctx.actions.run(
        outputs = [output],
        inputs = [src] + cc_toolchain.all_files.to_list(),
        arguments = [
            "--output-target",
            out_format,
            src.path,
            output.path,
        ],
        executable = cc_toolchain.objcopy_executable,
    )
    return output

def obj_disassemble(ctx, **kwargs):
    """Disassemble an input file.

    Args:
      ctx: The context object for this rule.
      kwargs: Overrides of values normally retrived from the context object.
        output: The name of the output file.  Constructed from `name` if not
                specified.
        src: The src File object.
    Returns:
      The disassembled File.
    """
    cc_toolchain = find_cc_toolchain(ctx).cc
    output = kwargs.get("output")
    if not output:
        name = get_override(ctx, "attr.name", kwargs)
        output = "{}.dis".format(name)

    output = ctx.actions.declare_file(output)
    src = get_override(ctx, "attr.src", kwargs)
    cleanup_script = get_override(ctx, "file._cleanup_script", kwargs)

    ctx.actions.run_shell(
        tools = [cleanup_script],
        outputs = [output],
        inputs = [src] + cc_toolchain.all_files.to_list(),
        arguments = [
            cc_toolchain.objdump_executable,
            src.path,
            cleanup_script.path,
            output.path,
        ],
        execution_requirements = {
            "no-sandbox": "",
        },
        command = "$1 -wx --disassemble --line-numbers --disassemble-zeroes --source --visualize-jumps $2 | $3 > $4",
    )
    return output

def convert_to_vmem(ctx, **kwargs):
    """Transform a binary to a VMEM file.

    Args:
      ctx: The context object for this rule.
      kwargs: Overrides of values normally retrived from the context object.
        output: The name of the output file.  Constructed from `name` and `suffix`
                 if not specified.
        src: The src File object.
        format: The objcopy output-format.
    Returns:
      The transformed File.
    """
    output = kwargs.get("output")
    word_size = get_override(ctx, "attr.word_size", kwargs)
    if not output:
        name = get_override(ctx, "attr.name", kwargs)
        output = "{}.{}.vmem".format(name, word_size)

    output = ctx.actions.declare_file(output)
    src = get_override(ctx, "attr.src", kwargs)

    ctx.actions.run(
        outputs = [output],
        inputs = [src],
        arguments = [
            src.path,
            "--binary",
            # Reverse the endianness of every word.
            "--offset",
            "0x0",
            "--byte-swap",
            str(word_size // 8),
            # Pad to word alignment
            "--fill",
            "0xff",
            "-within",
            src.path,
            "-binary",
            "-range-pad",
            str(word_size // 8),
            # Output a VMEM file with specified word size
            "--output",
            output.path,
            "--vmem",
            str(word_size),
        ],
        # This this executable is expected to be installed (as required by the
        # srecord package in apt-requirements.txt).
        executable = "srec_cat",
        use_default_shell_env = True,
    )
    return output
