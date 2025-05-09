# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("//rules:stamp.bzl", "stamp_attr", "stamping_enabled")
load("//rules/opentitan:hw.bzl", "OpenTitanTopInfo", "opentitan_top_get_ip_attr")
load("//rules:doxygen.bzl", "DoxygenCcInputInfo")

"""Autogeneration rules for OpenTitan.

The rules in this file are for autogenerating various file resources
used by the OpenTitan build, such as register definition files generated
from hjson register descriptions.
"""

def _opentitan_ip_c_header_impl(ctx):
    header = ctx.actions.declare_file("{}_regs.h".format(ctx.attr.ip))
    top = ctx.attr.top[OpenTitanTopInfo]
    hjson = opentitan_top_get_ip_attr(top, ctx.attr.ip, "hjson")

    arguments = [
        "-D",
        "-q",
        "-o",
        header.path,
        hjson.path,
    ]
    inputs = [hjson]

    # Add path to an alias path if it's needed.
    if ctx.file.alias:
        alias = ctx.file.alias

        # add the alias argument.
        arguments.extend([
            "--alias",
            alias.path,
        ])

        # add the alias as an input file.
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
        DoxygenCcInputInfo(
            files = depset([header]),
            include_paths = depset([header.dirname]),
        ),
    ]

opentitan_ip_c_header = rule(
    implementation = _opentitan_ip_c_header_impl,
    doc = "Generate the C headers for an IP block as used in a top",
    attrs = {
        "top": attr.label(providers = [OpenTitanTopInfo], doc = "Opentitan top description"),
        "ip": attr.string(doc = "Name of the IP block"),
        "alias": attr.label(
            mandatory = False,
            allow_single_file = True,
            doc = "A path to an alias file",
        ),
        "_regtool": attr.label(
            default = "//util:regtool",
            executable = True,
            cfg = "exec",
        ),
    },
    provides = [CcInfo, DoxygenCcInputInfo],
)

def _opentitan_ip_rust_header_impl(ctx):
    tock = ctx.actions.declare_file("{}.rs".format(ctx.attr.ip))
    top = ctx.attr.top[OpenTitanTopInfo]
    hjson = opentitan_top_get_ip_attr(top, ctx.attr.ip, "hjson")

    stamp_args = []
    stamp_files = []
    if stamping_enabled(ctx):
        stamp_files = [ctx.version_file]
        stamp_args.append("--version-stamp={}".format(ctx.version_file.path))

    ctx.actions.run(
        outputs = [tock],
        inputs = [hjson] + stamp_files,
        arguments = [
            "--tock",
            "-q",
            "-o",
            tock.path,
        ] + stamp_args + [hjson.path],
        executable = ctx.executable._regtool,
    )

    return [
        DefaultInfo(files = depset([tock])),
        OutputGroupInfo(
            tock = depset([tock]),
        ),
    ]

opentitan_ip_rust_header = rule(
    implementation = _opentitan_ip_rust_header_impl,
    doc = "Generate the Rust headers for an IP block as used in a top",
    attrs = {
        "top": attr.label(providers = [OpenTitanTopInfo], doc = "Opentitan top description"),
        "ip": attr.string(doc = "Name of the IP block"),
        "_regtool": attr.label(
            default = "//util:regtool",
            executable = True,
            cfg = "exec",
        ),
    } | stamp_attr(-1, "//rules:stamp_flag"),
)

def _opentitan_autogen_dif_gen(ctx):
    outputs = []
    outdir = "{}/{}".format(ctx.bin_dir.path, ctx.label.package)
    top = ctx.attr.top[OpenTitanTopInfo]
    ip_hjson = opentitan_top_get_ip_attr(top, ctx.attr.ip, "hjson")

    groups = {}
    for group, files in ctx.attr.output_groups.items():
        deps = []
        for file in files:
            deps.append(ctx.actions.declare_file(file))
        outputs.extend(deps)
        groups[group] = depset(deps)

    inputs = [ip_hjson]

    arguments = [
        "--ipcfg",
        ip_hjson.path,
        "--outdir",
        outdir,
    ]

    ctx.actions.run(
        outputs = outputs,
        inputs = inputs,
        arguments = arguments,
        executable = ctx.executable._autogen_dif,
    )

    return [
        DefaultInfo(files = depset(outputs)),
        OutputGroupInfo(**groups),
    ]

opentitan_autogen_dif_gen = rule(
    implementation = _opentitan_autogen_dif_gen,
    doc = "Generate the DIFs file for an IP",
    attrs = {
        "top": attr.label(mandatory = True, providers = [OpenTitanTopInfo], doc = "Opentitan top description"),
        "ip": attr.string(mandatory = True, doc = "Name of the IP for which to generate the DIF"),
        "output_groups": attr.string_list_dict(
            allow_empty = True,
            doc = """
                Mappings from output group names to lists of paths contained in
                that group.
            """,
        ),
        "_autogen_dif": attr.label(
            default = "//util:autogen_dif",
            executable = True,
            cfg = "exec",
        ),
    },
)

# See opentitan_autogen_dif_gen for documentation of parameters.
def opentitan_autogen_dif(name, top, ip, deps = [], target_compatible_with = []):
    opentitan_autogen_dif_gen(
        name = "{}_gen".format(name),
        top = top,
        ip = ip,
        output_groups = {
            "hdr": ["dif_{}_autogen.h".format(ip)],
            "src": ["dif_{}_autogen.c".format(ip)],
            "unittest": ["dif_{}_autogen_unittest.cc".format(ip)],
        },
        target_compatible_with = target_compatible_with,
    )

    for grp in ["hdr", "src", "unittest"]:
        native.filegroup(
            name = "{}_{}".format(name, grp),
            srcs = [":{}_gen".format(name)],
            output_group = grp,
        )

    native.cc_library(
        name = name,
        srcs = [":{}_src".format(name)],
        hdrs = [":{}_hdr".format(name)],
        deps = deps,
    )

def _opentitan_top_dt_gen(ctx):
    outputs = []
    outdir = "{}/{}".format(ctx.bin_dir.path, ctx.label.package)

    groups = {}
    for group, files in ctx.attr.output_groups.items():
        deps = []
        for file in files:
            deps.append(ctx.actions.declare_file(file))
        outputs.extend(deps)
        groups[group] = depset(deps)

    top = ctx.attr.top[OpenTitanTopInfo]

    inputs = [top.hjson]
    tools = []
    ips = []
    for ipname in top.ip_map:
        if ctx.attr.gen_top or ipname in ctx.attr.gen_ips:
            hjson = opentitan_top_get_ip_attr(top, ipname, "hjson")
            inputs.append(hjson)
            ips.extend(["-i", hjson.path])
            ipconfig = opentitan_top_get_ip_attr(top, ipname, "ipconfig", required = False)
            if ipconfig:
                inputs.append(ipconfig)
                ips.extend(["--ipconfig", ipconfig.path])
            extension = opentitan_top_get_ip_attr(top, ipname, "extension", required = False, output = "target")
            if extension:
                ext_files = extension[DefaultInfo].files.to_list()
                if len(ext_files) > 1:
                    fail("opentitan_top_dt_gen was given {} as an extension but it contains more one file: {}"
                        .format(extension, ext_files))
                tools.append(extension[DefaultInfo].default_runfiles.files)
                ips.extend(["--extension", ext_files[0].path])

    arguments = [
        "--topgencfg",
        top.hjson.path,
        "--outdir",
        outdir,
    ]
    arguments.append("--gen-top" if ctx.attr.gen_top else "--gen-ip")
    for ipname in ctx.attr.gen_ips:
        if ipname not in top.ip_map:
            fail("Cannot generate IP headers: top {} does not contain IP {}".format(top.name, ipname))

    arguments.extend(ips)

    ctx.actions.run(
        outputs = outputs,
        inputs = inputs,
        arguments = arguments,
        executable = ctx.executable._dttool,
        tools = tools,
    )

    return [
        DefaultInfo(files = depset(outputs)),
        OutputGroupInfo(**groups),
    ]

opentitan_top_dt_gen = rule(
    implementation = _opentitan_top_dt_gen,
    doc = "Generate the C headers for an IP block as used in a top",
    attrs = {
        "top": attr.label(providers = [OpenTitanTopInfo], doc = "Opentitan top description"),
        "gen_top": attr.bool(default = False, doc = "If true, generate the toplevel files"),
        "gen_ips": attr.string_list(doc = "List of IPs for which to generate header files"),
        "output_groups": attr.string_list_dict(
            allow_empty = True,
            doc = """
                Mappings from output group names to lists of paths contained in
                that group.
            """,
        ),
        "_dttool": attr.label(
            default = "//util:dttool",
            executable = True,
            cfg = "exec",
        ),
    },
)

def opentitan_ip_dt_header(name, top, ip, deps = None, target_compatible_with = []):
    """
    Generate the C header for an IP block as used in a top. This library is created to the
    provided top and can have additional dependencies. The top target must export an
    OpenTitanTopInfo provider, e.g. by created by opentitan_top. If this IP is not included
    in the top, an error will be thrown.
    """
    if deps == None:
        deps = []
    if target_compatible_with == None:
        target_compatible_with = []

    opentitan_top_dt_gen(
        name = "{}_gen".format(name),
        top = top,
        gen_ips = [ip],
        output_groups = {
            "hdr": ["dt/dt_{}.h".format(ip)],
            "src": ["dt/dt_{}.c".format(ip)],
        },
        target_compatible_with = target_compatible_with,
    )

    for grp in ["hdr", "src"]:
        native.filegroup(
            name = "{}_{}".format(name, grp),
            srcs = [":{}_gen".format(name)],
            output_group = grp,
        )

def opentitan_top_dt_api(name, top, deps = None):
    """
    Create a library that exports the "dt_api.h" header. This library is created to the
    provided top and can have additional dependencies. The top target must export an
    OpenTitanTopInfo provider, e.g. by created by opentitan_top.
    """
    if deps == None:
        deps = []

    opentitan_top_dt_gen(
        name = "{}_gen".format(name),
        top = top,
        gen_top = True,
        output_groups = {
            "hdr": ["dt/dt_api.h"],
            "src": ["dt/dt_api.c"],
        },
    )

    for grp in ["src", "hdr"]:
        native.filegroup(
            name = "{}_{}".format(name, grp),
            srcs = [":{}_gen".format(name)],
            output_group = grp,
        )

    native.cc_library(
        name = name,
        srcs = [":{}_src".format(name)],
        hdrs = [":{}_hdr".format(name)],
        deps = deps,
        # Make the dt_api.h header accessible as "dt/dt_api.h".
        includes = ["."],
    )

def _opentitan_autogen_testutils_gen(ctx):
    outputs = []
    top = ctx.attr.top[OpenTitanTopInfo]
    groups = {}
    for group, files in ctx.attr.output_groups.items():
        deps = []
        for file in files:
            deps.append(ctx.actions.declare_file(file))
        outputs.extend(deps)
        groups[group] = depset(deps)
    inputs = [top.hjson]
    arguments = [
        "--topcfg",
        top.hjson.path,
        "--outdir",
        outputs[0].dirname,
        "--clang-format",
        ctx.executable._clang_format.path,
    ]
    for ip in top.ip_map.keys():
        ip_hjson = opentitan_top_get_ip_attr(top, ip, "hjson")
        inputs.append(ip_hjson)
        arguments.extend(["-i", ip_hjson.path])

    # Generate files
    ctx.actions.run(
        outputs = outputs,
        inputs = inputs,
        arguments = arguments,
        executable = ctx.executable._autogen_testutils,
        tools = [ctx.executable._clang_format],
    )

    return [
        DefaultInfo(files = depset(outputs)),
        OutputGroupInfo(**groups),
    ]

opentitan_autogen_testutils_gen = rule(
    implementation = _opentitan_autogen_testutils_gen,
    doc = "Generate the testutils file for a top",
    attrs = {
        "top": attr.label(mandatory = True, providers = [OpenTitanTopInfo], doc = "Opentitan top description"),
        "output_groups": attr.string_list_dict(
            allow_empty = True,
            doc = """
                Mappings from output group names to lists of paths contained in
                that group.
            """,
        ),
        "_autogen_testutils": attr.label(
            default = "//util:gen_testutils",
            executable = True,
            cfg = "exec",
        ),
        "_clang_format": attr.label(
            default = "@lowrisc_rv32imcb_toolchain//:bin/clang-format",
            allow_single_file = True,
            cfg = "host",
            executable = True,
            doc = "The clang-format executable",
        ),
    },
)

# See opentitan_autogen_testutils_gen for documentation of parameters.
def opentitan_autogen_isr_testutils(name, top, deps = [], target_compatible_with = []):
    opentitan_autogen_testutils_gen(
        name = "{}_gen".format(name),
        top = top,
        output_groups = {
            "hdr": ["isr_testutils.h"],
            "src": ["isr_testutils.c"],
        },
    )
    for grp in ["hdr", "src"]:
        native.filegroup(
            name = "{}_{}".format(name, grp),
            srcs = [":{}_gen".format(name)],
            output_group = grp,
        )
    native.cc_library(
        name = name,
        srcs = [":{}_src".format(name)],
        hdrs = [":{}_hdr".format(name)],
        deps = deps,
        target_compatible_with = target_compatible_with,
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
