# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("@lowrisc_opentitan//rules:stamp.bzl", "stamp_attr", "stamping_enabled")
load("@lowrisc_opentitan//rules/opentitan:util.bzl", "flatten")
load("@lowrisc_opentitan//rules:doxygen.bzl", "DoxygenCcInputInfo")
load(
    "@lowrisc_opentitan//hw/top:defs.bzl",
    "opentitan_require_ip_attr",
    "opentitan_require_top_attr",
    "opentitan_select_ip_attr",
)

"""Autogeneration rules for OpenTitan.

The rules in this file are for autogenerating various file resources
used by the OpenTitan build, such as register definition files generated
from hjson register descriptions.
"""

def _opentitan_ip_c_header_impl(ctx):
    header = ctx.actions.declare_file("{}_regs.h".format(ctx.attr.ip))

    arguments = [
        "-D",
        "-q",
        "-o",
        header.path,
        ctx.file.hjson.path,
    ]
    inputs = [ctx.file.hjson]

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

opentitan_ip_c_header_rule = rule(
    implementation = _opentitan_ip_c_header_impl,
    doc = "Generate the C headers for an IP block as used in a top",
    attrs = {
        "ip": attr.string(mandatory = True, doc = "Name of the IP"),
        "hjson": attr.label(allow_single_file = True, doc = "Hjson description of the IP"),
        "alias": attr.label(
            mandatory = False,
            allow_single_file = True,
            doc = "A path to an alias file",
        ),
        "_regtool": attr.label(
            default = "@lowrisc_opentitan//util:regtool",
            executable = True,
            cfg = "exec",
        ),
    },
    provides = [CcInfo, DoxygenCcInputInfo],
)

def opentitan_ip_c_header(name, ip, target_compatible_with = [], **kwargs):
    """
    Macro around `opentitan_ip_c_header_rule` that automatically sets `hjson` for the current top.
    The target will also be marked as compatible only with tops containing this IP.
    """
    opentitan_ip_c_header_rule(
        name = name,
        ip = ip,
        hjson = opentitan_select_ip_attr(ip, "hjson"),
        target_compatible_with = target_compatible_with + opentitan_require_ip_attr(ip, "hjson"),
        **kwargs
    )

def _opentitan_ip_rust_header_impl(ctx):
    tock = ctx.actions.declare_file("{}.rs".format(ctx.attr.ip))

    stamp_args = []
    stamp_files = []
    if stamping_enabled(ctx):
        stamp_files = [ctx.version_file]
        stamp_args.append("--version-stamp={}".format(ctx.version_file.path))

    ctx.actions.run(
        outputs = [tock],
        inputs = [ctx.file.hjson] + stamp_files,
        arguments = [
            "--tock",
            "-q",
            "-o",
            tock.path,
        ] + stamp_args + [ctx.file.hjson.path],
        executable = ctx.executable._regtool,
    )

    return [
        DefaultInfo(files = depset([tock])),
        OutputGroupInfo(
            tock = depset([tock]),
        ),
    ]

opentitan_ip_rust_header_rule = rule(
    implementation = _opentitan_ip_rust_header_impl,
    doc = "Generate the Rust headers for an IP block as used in a top",
    attrs = {
        "hjson": attr.label(allow_single_file = True, doc = "Hjson description of the IP"),
        "ip": attr.string(doc = "Name of the IP block"),
        "_regtool": attr.label(
            default = "@lowrisc_opentitan//util:regtool",
            executable = True,
            cfg = "exec",
        ),
    } | stamp_attr(-1, "@lowrisc_opentitan//rules:stamp_flag"),
)

def opentitan_ip_rust_header(name, ip, target_compatible_with = [], **kwargs):
    """
    Macro around `opentitan_ip_rust_header_rule` that automatically sets `hjson` for the current top.
    The target will also be marked as compatible only with tops containing this IP.
    """
    opentitan_ip_rust_header_rule(
        name = name,
        ip = ip,
        hjson = opentitan_select_ip_attr(ip, "hjson"),
        target_compatible_with = target_compatible_with + opentitan_require_ip_attr(ip, "hjson"),
        **kwargs
    )

def _opentitan_autogen_dif_gen(ctx):
    outputs = []

    groups = {}
    for group, files in ctx.attr.output_groups.items():
        deps = []
        for file in files:
            deps.append(ctx.actions.declare_file(file))
        outputs.extend(deps)
        groups[group] = depset(deps)

    inputs = [ctx.file.hjson]

    arguments = [
        "--ipcfg",
        ctx.file.hjson.path,
        "--outdir",
        outputs[0].dirname,
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
        "hjson": attr.label(allow_single_file = True, doc = "Hjson description of the IP"),
        "ip": attr.string(mandatory = True, doc = "Name of the IP for which to generate the DIF"),
        "output_groups": attr.string_list_dict(
            allow_empty = True,
            doc = """
                Mappings from output group names to lists of paths contained in
                that group.
            """,
        ),
        "_autogen_dif": attr.label(
            default = "@lowrisc_opentitan//util:autogen_dif",
            executable = True,
            cfg = "exec",
        ),
    },
)

def opentitan_autogen_dif(name, ip, deps = [], target_compatible_with = []):
    """
    Macro around `opentitan_autogen_dif_gen` that automatically sets `hjson` for the current top
    and `output_groups` to the default ones.
    The target will also be marked as compatible only with tops containing this IP.

    This macro also creates some filegroups to extract the sources, headers and unittests, as
    well as a `cc_library` for the DIF code which will depend on `deps`.
    """
    opentitan_autogen_dif_gen(
        name = "{}_gen".format(name),
        hjson = opentitan_select_ip_attr(ip, "hjson"),
        ip = ip,
        output_groups = {
            "hdr": ["dif_{}_autogen.h".format(ip)],
            "src": ["dif_{}_autogen.c".format(ip)],
            "unittest": ["dif_{}_autogen_unittest.cc".format(ip)],
        },
        target_compatible_with = target_compatible_with + opentitan_require_ip_attr(ip, "hjson"),
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
    _subdir_ignore = ctx.actions.declare_directory("_ignore_{}".format(ctx.label.name))
    outdir = _subdir_ignore.dirname

    groups = {}
    for group, files in ctx.attr.output_groups.items():
        deps = []
        for file in files:
            f = ctx.actions.declare_file(file)
            deps.append(f)
        outputs.extend(deps)
        groups[group] = depset(deps)

    arguments = [
        "--topgencfg",
        ctx.file.top_hjson.path,
        "--outdir",
        outdir,
    ]
    inputs = [ctx.file.top_hjson]
    tools = []
    ips = []

    if ctx.attr.gen_top:
        arguments.append("--gen-top")
    if ctx.attr.gen_ip:
        arguments.append("--gen-ip")
    for hjson in ctx.files.ips_hjson:
        inputs.append(hjson)
        arguments.extend(["-i", hjson.path])
    for ipconfig in ctx.files.ips_config:
        inputs.append(ipconfig)
        arguments.extend(["--ipconfig", ipconfig.path])
    for extension in ctx.attr.extensions:
        ext_files = extension[DefaultInfo].files.to_list()
        if len(ext_files) > 1:
            fail("opentitan_top_dt_gen was given {} as an extension but it contains more one file: {}"
                .format(extension, ext_files))
        tools.append(extension[DefaultInfo].default_runfiles.files)
        arguments.extend(["--extension", ext_files[0].path])

    ctx.actions.run(
        outputs = outputs + [_subdir_ignore],
        inputs = inputs,
        arguments = arguments,
        executable = ctx.executable._dttool,
        tools = tools,
    )

    return [
        DefaultInfo(files = depset(outputs)),
        OutputGroupInfo(**groups),
    ]

opentitan_top_dt_gen_rule = rule(
    implementation = _opentitan_top_dt_gen,
    doc = "Generate the C headers for an IP block as used in a top",
    attrs = {
        "gen_top": attr.bool(default = False, doc = "If true, generate the toplevel files"),
        "gen_ip": attr.bool(default = False, doc = "If true, generate the IP files"),
        "top_hjson": attr.label(allow_single_file = True, doc = "Hjson description of the top"),
        "ips_hjson": attr.label_list(allow_files = True, doc = "List of Hjson descriptions of IPs"),
        "ips_config": attr.label_list(allow_files = True, doc = "List of Hjson ipconfigs of IPs"),
        "extensions": attr.label_list(allow_files = True, cfg = "exec", doc = "List of dtgen extensions"),
        "output_groups": attr.string_list_dict(
            allow_empty = True,
            doc = """
                Mappings from output group names to lists of paths contained in
                that group.
            """,
        ),
        "_dttool": attr.label(
            default = "@lowrisc_opentitan//util:dttool",
            executable = True,
            cfg = "exec",
        ),
    },
)

def opentitan_top_dt_gen(name, gen_ips = [], gen_top = False, output_groups = {}, target_compatible_with = []):
    opentitan_top_dt_gen_rule(
        name = name,
        gen_top = gen_top,
        gen_ip = len(gen_ips) > 0,
        ips_hjson = flatten([
            # Trick: we wrap the attribute in a list and return the empty list if the attribute (or the IP) is
            # missing. This way we can simply concatenate all the selects.
            opentitan_select_ip_attr(ip, "hjson", required = False, default = [], fn = lambda x: [x])
            for ip in gen_ips
        ]),
        ips_config = flatten([
            opentitan_select_ip_attr(ip, "ipconfig", required = False, default = [], fn = lambda x: [x])
            for ip in gen_ips
        ]),
        extensions = flatten([
            opentitan_select_ip_attr(ip, "extension", required = False, default = [], fn = lambda x: [x])
            for ip in gen_ips
        ]),
        output_groups = output_groups,
        top_hjson = "@lowrisc_opentitan//hw/top:top_gen_hjson",
        target_compatible_with = target_compatible_with + opentitan_require_top_attr("hjson") + flatten([
            opentitan_require_ip_attr(ip, "hjson")
            for ip in gen_ips
        ]),
    )

def opentitan_ip_dt(name, ip, target_compatible_with = []):
    """
    Generate the C header/source for an IP block as used in the current top.
    The target will also be marked as compatible only with tops containing this IP.
    Specifically, three targets will be created:
    - <name>_gen: rule generating all files
    - <name>_src: filegroup containing only the source file of <name>_gen
    - <name>_hdr: filegroup containing only the header file of <name>_gen
    """
    if target_compatible_with == None:
        target_compatible_with = []

    opentitan_top_dt_gen(
        name = "{}_gen".format(name),
        gen_ips = [ip],
        output_groups = {
            "hdr": ["{}.h".format(ip)],
            "src": ["{}.c".format(ip)],
        },
        target_compatible_with = target_compatible_with,
    )

    for grp in ["hdr", "src"]:
        native.filegroup(
            name = "{}_{}".format(name, grp),
            srcs = [":{}_gen".format(name)],
            output_group = grp,
        )

def opentitan_top_dt_api(name, deps = None):
    """
    Create a library that exports the "dt_api.h" header.
    The target will also be marked as compatible only with tops containing this IP.
    Additionally, a `cc_library` will be created from this header with additional
    dependencies on `deps`.
    """
    if deps == None:
        deps = []

    opentitan_top_dt_gen(
        name = "{}_gen".format(name),
        gen_top = True,
        output_groups = {
            "hdr": ["api.h"],
            "src": ["api.c"],
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
    )

def _opentitan_autogen_testutils_gen(ctx):
    outputs = []
    groups = {}
    for group, files in ctx.attr.output_groups.items():
        deps = []
        for file in files:
            deps.append(ctx.actions.declare_file(file))
        outputs.extend(deps)
        groups[group] = depset(deps)
    inputs = [ctx.file.top_hjson]
    arguments = [
        "--topcfg",
        ctx.file.top_hjson.path,
        "--outdir",
        outputs[0].dirname,
        "--clang-format",
        ctx.executable._clang_format.path,
    ]
    for ip_hjson in ctx.files.ips_hjson:
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
        "top_hjson": attr.label(allow_single_file = True, doc = "Hjson description of the top"),
        "ips_hjson": attr.label_list(allow_files = True, doc = "List of Hjson descriptions of IPs"),
        "output_groups": attr.string_list_dict(
            allow_empty = True,
            doc = """
                Mappings from output group names to lists of paths contained in
                that group.
            """,
        ),
        "_autogen_testutils": attr.label(
            default = "@lowrisc_opentitan//util:gen_testutils",
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

def opentitan_autogen_isr_testutils(name, ips = [], deps = [], target_compatible_with = []):
    """
    Macro around `opentitan_autogen_testutils_gen` that automatically sets `top_hjson` for the current top,
    `ips_hjson` to the list of all IPs listed in `ips` for the top and `output_groups` to the expected value for the
    `irs_testutils`.

    This macro also creates some filegroups to extract the sources, headers and unittests, as
    well as a `cc_library` for the testutil code which will depend on `deps`.
    """
    opentitan_autogen_testutils_gen(
        name = "{}_gen".format(name),
        ips_hjson = flatten([
            # Trick: we wrap the attribute in a list and return the empty list of the attribute (or the IP) is
            # missing. This way we can simply concatenate all the selects.
            opentitan_select_ip_attr(ip, "hjson", required = False, default = [], fn = lambda x: [x])
            for ip in ips
        ]),
        top_hjson = "@lowrisc_opentitan//hw/top:top_gen_hjson",
        output_groups = {
            "hdr": ["isr_testutils.h"],
            "src": ["isr_testutils.c"],
        },
        target_compatible_with = opentitan_require_top_attr("hjson"),
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
            default = "@lowrisc_opentitan//util:rom_chip_info",
            executable = True,
            cfg = "exec",
        ),
    } | stamp_attr(-1, "@lowrisc_opentitan//rules:stamp_flag"),
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
        hdrs = ["@lowrisc_opentitan//sw/device/silicon_creator/lib:chip_info.h"],
        deps = [
            "@lowrisc_opentitan//sw/device/lib/base:macros",
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
            default = "@lowrisc_opentitan//sw/device/tests/crypto:ecdsa_p256_verify_set_testvectors",
            executable = True,
            cfg = "exec",
        ),
    },
)

def _autogen_stamp_include(ctx):
    """
    Bazel rule for generating C header containing all stamping variables.

    This rule is instantiated as //rules:autogen_stamp_include.
    Please see the entry in rules/BUILD for explanation.
    """
    output = ctx.actions.declare_file("{}.inc".format(ctx.attr.name))

    if stamping_enabled(ctx):
        ctx.actions.run_shell(
            outputs = [output],
            inputs = [ctx.version_file, ctx.info_file],
            arguments = [
                ctx.version_file.path,
                ctx.info_file.path,
                output.path,
            ],
            command = """
                cat $1 $2 \
                | sed -E 's/^(\\w+) (.*)/#define BAZEL_\\1 \\2/' \
                > $3
            """,
        )
    else:
        ctx.actions.write(output, "")

    return [
        DefaultInfo(files = depset([output])),
    ]

autogen_stamp_include = rule(
    implementation = _autogen_stamp_include,
    attrs = stamp_attr(-1, "@lowrisc_opentitan//rules:stamp_flag"),
)
