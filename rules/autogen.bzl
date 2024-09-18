# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("//rules:stamp.bzl", "stamp_attr", "stamping_enabled")

"""Autogeneration rules for OpenTitan.

The rules in this file are for autogenerating various file resources
used by the OpenTitan build, such as register definition files generated
from hjson register descriptions.
"""

def _hjson_c_header(ctx):
    output_stem = (ctx.attr.output_stem if ctx.attr.output_stem else ctx.label.name.replace("_c_", "_"))
    header = ctx.actions.declare_file("{}.h".format(output_stem))
    node = []
    if ctx.attr.node:
        node.append("--node={}".format(ctx.attr.node))

    arguments = [
        "-D",
        "-q",
        "-o",
        header.path,
    ] + node + [src.path for src in ctx.files.srcs]

    # `inputs = ctx.files.srcs` will create `inputs` as an immutable list
    # so need to unpack like this before appending the alias later
    inputs = list(ctx.files.srcs)

    # add path to an alias path if it's needed
    if ctx.attr.alias:
        alias = ctx.file.alias

        # add the alias argument
        arguments.extend([
            "--alias",
            alias.path,
        ])

        # add the alias as an input file
        inputs.append(alias)

    ctx.actions.run(
        outputs = [header],
        inputs = inputs,
        arguments = arguments,
        executable = ctx.executable._regtool,
    )

    return [
        CcInfo(compilation_context = cc_common.create_compilation_context(
            includes = depset([header.dirname]),
            headers = depset([header]),
        )),
        DefaultInfo(files = depset([header])),
        OutputGroupInfo(
            header = depset([header]),
        ),
    ]

autogen_hjson_c_header = rule(
    implementation = _hjson_c_header,
    attrs = {
        "srcs": attr.label_list(allow_files = True),
        "node": attr.string(
            doc = "Register block node to generate",
        ),
        "alias": attr.label(
            mandatory = False,
            allow_single_file = True,
            doc = "A path to an alias file",
        ),
        "output_stem": attr.string(
            doc = """
                The name of the output file with no suffix.
                This is optional, and if not given it will be set to the
                target name replacing "_c_" by "_".
                """,
        ),
        "_regtool": attr.label(
            default = "//util:regtool",
            executable = True,
            cfg = "exec",
        ),
    },
)

def _hjson_dt_header(ctx):
    output_stem = (ctx.attr.output_stem if ctx.attr.output_stem else "dt_" + ctx.label.name.replace("_dt", ""))
    header = ctx.actions.declare_file("{}.h".format(output_stem))
    node = []
    if ctx.attr.node:
        node.append("--default-node={}".format(ctx.attr.node))

    arguments = [
        "--gen-ip",
        "--outdir",
        header.dirname,
    ] + node

    for f in ctx.files.srcs:
        arguments.extend(["-i", f.path])

    ctx.actions.run(
        outputs = [header],
        inputs = ctx.files.srcs,
        arguments = arguments,
        executable = ctx.executable._dttool,
    )

    cc_infos = [dep[CcInfo] for dep in ctx.attr.deps if CcInfo in dep]

    cc_infos.append(
        CcInfo(compilation_context = cc_common.create_compilation_context(
            includes = depset([header.dirname]),
            headers = depset([header]),
        ))
    )

    return [
        cc_common.merge_cc_infos(cc_infos = cc_infos),
        DefaultInfo(files = depset([header], transitive=[dep[DefaultInfo].files for dep in ctx.attr.deps])),
        OutputGroupInfo(
            header = depset([header]),
        ),
    ]

autogen_hjson_dt_header = rule(
    implementation = _hjson_dt_header,
    attrs = {
        "srcs": attr.label_list(allow_files = True),
        "node": attr.string(
            doc = "Register block node to make the default",
        ),
        "output_stem": attr.string(
            doc = """
                The name of the output file with no suffix.
                This is optional, and if not given it will be set to the
                target name without the "_dt" suffix and with the "dt_" prefix.
                """,
        ),
        "deps": attr.label_list(
            doc = "Dependencies to compile the header.",
            default = ["//hw/top:dt_api"],
        ),
        "_dttool": attr.label(
            default = "//util:dttool",
            executable = True,
            cfg = "exec",
        ),
    },
)

def _hjson_rust_header(ctx):
    node = []
    if ctx.attr.node:
        node.append("--node={}".format(ctx.attr.node))
    stamp_args = []
    stamp_files = []
    if stamping_enabled(ctx):
        stamp_files = [ctx.version_file]
        stamp_args.append("--version-stamp={}".format(ctx.version_file.path))

    output_stem = (ctx.attr.output_stem if ctx.attr.output_stem else ctx.label.name.replace("_rust_", "_"))
    tock = ctx.actions.declare_file("{}.rs".format(output_stem))
    ctx.actions.run(
        outputs = [tock],
        inputs = ctx.files.srcs + [ctx.executable._regtool] + stamp_files,
        arguments = [
            "--tock",
            "-q",
            "-o",
            tock.path,
        ] + stamp_args + node + [src.path for src in ctx.files.srcs],
        executable = ctx.executable._regtool,
    )

    return [
        DefaultInfo(files = depset([tock])),
        OutputGroupInfo(
            tock = depset([tock]),
        ),
    ]

autogen_hjson_rust_header = rule(
    implementation = _hjson_rust_header,
    attrs = {
        "srcs": attr.label_list(allow_files = True),
        "node": attr.string(
            doc = "Register block node to generate",
        ),
        "output_stem": attr.string(
            doc = """
                The name of the output file with no suffix.
                This is optional, and if not given it will be set to the
                target name replacing "_rust_" by "_".
                """,
        ),
        "_regtool": attr.label(
            default = "//util:regtool",
            executable = True,
            cfg = "exec",
        ),
    } | stamp_attr(-1, "//rules:stamp_flag"),
)

def autogen_hjson_sw_headers(name_prefix, srcs, **kwargs):
    """
    Generate all IP-specific software headers. This macro will
    create the following targets:
    - `{name_prefix}_c_regs`: C headers with register definitions.
    - `{name_prefix}_rust_regs`: Rust register definitions.
    - `{name_prefix}_dt`: DT definitions.

    The following optional extra arguments are supported:
    - `node`: select the register block node for which to generate
              the definitions; for DT selects the default node.
    """
    autogen_hjson_c_header(
        name = "{}_c_regs".format(name_prefix),
        srcs = srcs,
        **kwargs
    )
    autogen_hjson_rust_header(
        name = "{}_rust_regs".format(name_prefix),
        srcs = srcs,
        **kwargs
    )
    autogen_hjson_dt_header(
        name = "{}_dt".format(name_prefix),
        srcs = srcs,
        **kwargs
    )

def _chip_info_src(ctx):
    stamp_args = []
    stamp_files = []
    if stamping_enabled(ctx):
        stamp_files = [ctx.version_file]
        stamp_args.append("--ot_version_file")
        stamp_args.append(ctx.version_file.path)
    else:
        print("NOTE: stamping is disabled, the chip_info section will use a fixed version string")
        stamp_args.append("--default_version")

        # The script expects a 20-character long hash: "OpenTitanOpenTitanOT"
        stamp_args.append("4f70656e546974616e4f70656e546974616e4f54")

    out_source = ctx.actions.declare_file("chip_info.c")
    ctx.actions.run(
        outputs = [
            out_source,
        ],
        inputs = [
            ctx.executable._tool,
        ] + stamp_files,
        arguments = [
            "-o",
            out_source.dirname,
        ] + stamp_args,
        executable = ctx.executable._tool,
    )

    return [
        DefaultInfo(files = depset([out_source])),
    ]

autogen_chip_info_src = rule(
    implementation = _chip_info_src,
    attrs = {
        "_tool": attr.label(
            default = "//util:rom_chip_info",
            executable = True,
            cfg = "exec",
        ),
    } | stamp_attr(-1, "//rules:stamp_flag"),
)

def autogen_chip_info(name):
    """Generates a cc_library named `name` that defines chip info."""

    # Generate a C source file that defines the chip info struct. This is an
    # implementation detail and should not be depended on externally.
    chip_info_src_target = name + "_gen_src"
    autogen_chip_info_src(name = chip_info_src_target)

    # Package up the generated source file with its corresponding header file
    # and dependencies. Any target that wants access to the chip info should
    # depend on this.
    native.cc_library(
        name = name,
        srcs = [chip_info_src_target],
        hdrs = ["//sw/device/silicon_creator/lib:chip_info.h"],
        deps = [
            "//sw/device/lib/base:macros",
        ],
    )

def _cryptotest_hjson_external(ctx):
    """
    Implementation of the Bazel rule for parsing externally-sourced test vectors.

    Crypto test vectors are represented in a standard HJSON format; for
    externally-sourced vectors, we need to parse the original data into the
    standard format before it can be used.

    This rule expects an executable script (the `parser` attribute) and a
    single external data file to pass to this script (the `src` attribute). It
    assumes that the parser accepts the following syntax:
      <script> <input file> dst.hjson

    ...where <input file> is the external test data and dst.hjson is the HJSON
    file to which the script writes the test vectors.
    """

    hjson = ctx.actions.declare_file(ctx.attr.name + ".hjson")
    parser_input = ctx.file.src
    ctx.actions.run(
        outputs = [hjson],
        inputs = [ctx.executable.parser, parser_input],
        arguments = [parser_input.path, hjson.path],
        executable = ctx.executable.parser,
    )

    return [
        DefaultInfo(files = depset([hjson])),
        OutputGroupInfo(
            hjson = depset([hjson]),
        ),
    ]

autogen_cryptotest_hjson_external = rule(
    implementation = _cryptotest_hjson_external,
    attrs = {
        "deps": attr.label_list(allow_files = True),
        "src": attr.label(allow_single_file = True),
        "parser": attr.label(
            mandatory = True,
            executable = True,
            cfg = "exec",
        ),
    },
)

def _cryptotest_header(ctx):
    """
    Implementation of the Bazel rule for generating crypto test vector headers.

    Crypto tests are all represented in a standard HJSON format. This rule runs
    an algorithm-specific script (the `test_setter` attribute) that reads an
    HJSON file (the `hjson` attribute) and populates a header template (the
    `template` attribute).

    Assumes that `test_setter` scripts accept the following syntax:
      <script> --template dst.h.tpl tests.hjson dst.h

    ...where dst.h.tpl is the header template, tests.hjson is the file
    containing the HJSON test vectors and dst.h is the header file to which the
    output will be written.
    """
    template = ctx.file.template
    if not template.basename.endswith(".h.tpl"):
        fail("Expected template to have a `.h.tpl` extension, got: " + str(ctx.files.srcs))
    header = ctx.actions.declare_file("{}/{}".format(ctx.label.name, template.basename[:-4]))

    hjson = ctx.file.hjson
    ctx.actions.run(
        outputs = [header],
        inputs = [template, hjson],
        arguments = [
            "-t",
            template.path,
            "-j",
            hjson.path,
            "-o",
            header.path,
        ],
        executable = ctx.executable.tool,
    )

    return [
        CcInfo(compilation_context = cc_common.create_compilation_context(
            includes = depset([header.dirname]),
            headers = depset([header]),
            defines = depset(["RULE_NAME=\"{}\"".format(ctx.label.name)]),
        )),
        DefaultInfo(files = depset([header]), default_runfiles = ctx.runfiles(files = [hjson])),
        OutputGroupInfo(
            header = depset([header]),
        ),
    ]

autogen_cryptotest_header = rule(
    implementation = _cryptotest_header,
    attrs = {
        "deps": attr.label_list(allow_files = True),
        "template": attr.label(mandatory = True, allow_single_file = [".tpl"]),
        "hjson": attr.label(mandatory = True, allow_single_file = [".hjson"]),
        "tool": attr.label(
            default = "//sw/device/tests/crypto:ecdsa_p256_verify_set_testvectors",
            executable = True,
            cfg = "exec",
        ),
    },
)

def _autogen_dttool_impl(ctx):
    # We output everything in the package directory.
    outdir = "{}/{}".format(ctx.bin_dir.path, ctx.label.package)
    outputs = []
    groups = {}
    for group, files in ctx.attr.output_groups.items():
        deps = []
        for f in files:
            # Declared files are relative to the package directory.
            deps.append(ctx.actions.declare_file(f))
        outputs.extend(deps)
        groups[group] = depset(deps)

    # Ignore the values since `dtgen` can recover them from the file content.
    ips = []
    for iphjson in ctx.files.ip_to_hjson:
        ips.extend(["-i", iphjson.path])

    ctx.actions.run(
        inputs = [ctx.file.top_gen_cfg] + ctx.files.ip_to_hjson + ctx.files.data,
        outputs = outputs,
        executable = ctx.executable._dttool,
        arguments = [
            "-t", ctx.file.top_gen_cfg.path,
            "--outdir", outdir,
            "--gen-top",
        ] + ips + ctx.attr.arguments,
        mnemonic = "DtGen",
        progress_message = "Running dttool on {}".format(ctx.file.top_gen_cfg.path),
    )
    return [
        DefaultInfo(
            files = depset(outputs),
        ),
        OutputGroupInfo(**groups),
    ]

autogen_dttool = rule(
    implementation = _autogen_dttool_impl,
    attrs = {
        "top_gen_cfg": attr.label(mandatory = True, allow_single_file = [".hjson"]),
        "ip_to_hjson": attr.label_keyed_string_dict(
            allow_files = True,
            default = {},
            doc = "Mapping from hjson files to IP names.",
        ),
        "output_groups": attr.string_list_dict(
            allow_empty = True,
            doc = "Mapping of group name to lists of files or directories in that named group (use '/' at the to make it a directory)",
        ),
        "data": attr.label_list(
            allow_files = True,
            # See https://bazel.build/reference/be/common-definitions#typical-attributes.
            doc = "Files needed by this rule at runtime. May list file or rule targets. Generally allows any target."
        ),
        "arguments": attr.string_list(
            default = [],
            doc = "Arguments to pass to the tool",
        ),
        "_dttool": attr.label(
            default = "//util:dttool",
            executable = True,
            cfg = "exec",
        ),
    }
)

def autogen_top_dt(
    topname,
    top_gen_cfg,
    ip_to_hjson,
    top_lib,
    dt_ip_deps,
    data = []):
    """
    TODO document
    """
    output_groups = {
        "dt_api": ["dt_api.h"],
        "dt_lib_srcs": ["devicetables.c"],
        "dt_lib_hdrs": ["devicetables.h"],
    }
    name = topname + "_dttool"
    # The output of this rule is a directory that contains everything.
    autogen_dttool(
        name = name,
        output_groups = output_groups,
        top_gen_cfg = top_gen_cfg,
        ip_to_hjson = ip_to_hjson,
        data = data
    )
    # Extract groups.
    for group in output_groups.keys():
        native.filegroup(
            name = "{}_{}".format(name, group),
            srcs = [":{}".format(name)],
            output_group = group,
        )
    # Create software artefacts.
    native.cc_library(
        name = "dt_api",
        hdrs = [":{}_dt_api".format(name)],
        deps = [top_lib],
        # Make the dt_api.h header accessible as "dt_api.h".
        includes = ["."],
    )

    native.cc_library(
        name = "devicetables",
        srcs = [":{}_dt_lib_srcs".format(name)],
        hdrs = [":{}_dt_lib_hdrs".format(name)],
        deps = [":dt_api"] + dt_ip_deps,
    )
