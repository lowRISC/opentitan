# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("//hw/top:defs.bzl", "ALL_TOP_NAMES")

DoxygenCcInputInfo = provider(
    fields = {
        "files": "depset of files",
        "include_paths": "depset of include paths",
    },
)

def _merge_doxygen_cc_input_infos(infos):
    """
    Given a list of DoxygenCcInputInfo, merge them into one by accumulating of files
    and include paths.

    Args:
      infos: List of DoxygenCcInputInfo.

    Returns: a DoxygenCcInputInfo.
    """
    return DoxygenCcInputInfo(
        files = depset(transitive = [getattr(info, "files", depset()) for info in infos]),
        include_paths = depset(transitive = [getattr(info, "include_paths", depset()) for info in infos]),
    )

def doxygen_gather_all_package_cc(name):
    """
    Create a `cc_library` targets which depends on all `cc_library` targets
    previously defined in the same BUILD file.
    """
    # We use a somewhat obscure feature of bazel that provides limited introspection.
    deps = [
        ":{}".format(name)
        for (name, info) in native.existing_rules().items()
        if info["kind"] == "cc_library"
    ]

    # Create a cc_library which depends on those.
    native.cc_library(
        name = name,
        deps = deps,
    )

def _gather_cc_files_impl(target, ctx):
    # Only propagate through cc_library.
    if ctx.rule.kind != "cc_library":
        return []
    files = []
    files.extend(ctx.rule.files.srcs)
    files.extend(ctx.rule.files.hdrs)
    infos = [DoxygenCcInputInfo(files = depset(files))]

    for dep in ctx.rule.attr.deps:
        # It can happen that a target does not have a Doxygen provider if
        # for example it returns a CcInfo but is not a cc_library rule, e.g.
        # `opentitan_ip_c_header`.
        if DoxygenCcInputInfo in dep:
            infos.append(dep[DoxygenCcInputInfo])

    return [_merge_doxygen_cc_input_infos(infos)]

_gather_cc_files = aspect(
    implementation = _gather_cc_files_impl,
    attr_aspects = ["deps"],
    required_providers = [CcInfo],
    doc = "Aspect used to inspect cc_library and extract the source/headers/deps."
)

def _doxygen_gather_cc_impl(ctx):
    include_paths = []
    infos = []

    for dep in ctx.attr.deps:
        if CcInfo in dep:
            cc = dep[CcInfo].compilation_context
            include_paths.append(cc.includes)
        doxy = dep[DoxygenCcInputInfo]
        infos.append(doxy)

    include_paths = depset(transitive = include_paths)
    all_infos = _merge_doxygen_cc_input_infos(infos + [DoxygenCcInputInfo(include_paths = include_paths)])

    return [
        DefaultInfo(files = all_infos.files),
        all_infos,
    ]

def _doxygen_gather_cc_transition_impl(settings, attr):
    platform = str(attr.platform) if attr.platform != None else settings["//command_line_option:platforms"]
    return {
        "//command_line_option:platforms": platform,
    }


doxygen_gather_cc = rule(
    implementation = _doxygen_gather_cc_impl,
    attrs = {
        "deps": attr.label_list(
            providers = [[CcInfo], [DoxygenCcInputInfo]],
            doc = "List of labels from which to gather the cc files",
            aspects = [_gather_cc_files],
        ),
        "platform": attr.label(
            doc = "If set, the rule will transition to the requested platform before gathering.",
        )
    },
    provides = [DoxygenCcInputInfo],
    cfg = transition(
        implementation = _doxygen_gather_cc_transition_impl,
        inputs = ["//command_line_option:platforms"],
        outputs = ["//command_line_option:platforms"],
    ),
    doc = """
This rule recursively gathers all source and headers files from cc_library.
More precisely, starting from the targets listed in `deps`, this rule will
proceed as follows:
- if the target exports a DoxygenCcInputInfo, it will add it to its list,
- if the target is defined by a `cc_library`, it will add the `srcs` and `hdrs`
  to its list and recursively gather files on all targets listed in `deps`.

The consolidated list of files will be returned in DoxygenCcInputInfo provider,
alongside the include paths found in the CcInfo from the targets.
"""
)

def _doxygen_multitop_dispatch(settings, attr):
    return {
        top_name: {
            "//hw/top": top_name
        }
        for top_name in ALL_TOP_NAMES
    }

def _doxygen_multitop_impl(ctx):
    infos = [src[DoxygenCcInputInfo] for src in ctx.attr.src]
    all_infos = _merge_doxygen_cc_input_infos(infos)
    return [
        DefaultInfo(files = all_infos.files),
        all_infos,
    ]

doxygen_multitop = rule(
    implementation = _doxygen_multitop_impl,
    attrs = {
        "src": attr.label(
            mandatory = True,
            doc = "Target generating the Doxygen sources",
            providers = [DoxygenCcInputInfo],
            cfg = transition(
                implementation = _doxygen_multitop_dispatch,
                inputs = [],
                outputs = ["//hw/top"],
            ),
        )
    }
)

def _doxygen_impl(ctx):
    # Put everything in the output in a directory
    output_dir = ctx.label.name

    # Declare a dictory just for the purpose of getting a clean path to the
    # output directory.
    _subdir_ignore = ctx.actions.declare_directory("{}/_ignore".format(output_dir))
    output_dir_path = _subdir_ignore.dirname
    print(output_dir_path)

    groups = {}
    outputs = []
    for group, files in ctx.attr.output_groups.items():
        deps = []
        for filename in files:
            name = "{}/{}".format(output_dir, filename)
            if filename.endswith("/"):
                deps.append(ctx.actions.declare_directory(name))
            else:
                deps.append(ctx.actions.declare_file(name))
        outputs.extend(deps)
        groups[group] = depset(deps)

    env = {
        name: ctx.expand_location(content, ctx.attr.data)
        for (name, content) in ctx.attr.env.items()
    } | {
        "DOXYGEN_OUT": output_dir_path,
    }
    substitutions = {
        name: ctx.expand_location(content, ctx.attr.data)
        for (name, content) in ctx.attr.substitutions.items()
    } | {
        "@@input@@": "\\\n".join(['"{}"'.format(src.path) for src in ctx.files.srcs]),
    }

    doxyfile = ctx.actions.declare_file("Doxyfile")
    ctx.actions.expand_template(
        template = ctx.file.doxyfile,
        output = doxyfile,
        substitutions = substitutions,
    )
    groups["doxyfile"] = [doxyfile]

    inputs = ctx.files.srcs + ctx.files.data + [doxyfile]

    ctx.actions.run(
        outputs = outputs + [_subdir_ignore],
        inputs = inputs,
        arguments = [doxyfile.path],
        executable = ctx.executable._doxygen,
        env = env,
    )

    return [
        DefaultInfo(files = depset(outputs + [doxyfile])),
        OutputGroupInfo(**groups),
    ]

doxygen = rule(
    implementation = _doxygen_impl,
    attrs = {
        "_doxygen": attr.label(
            default = "@doxygen//:doxygen_bin",
            allow_single_file = True,
            cfg = "exec",
            executable = True,
            doc = "Doxygen executable",
        ),
        "doxyfile": attr.label(
            allow_single_file = True,
            mandatory = True,
            doc = "Doxygen configuration file. The content will be expanded using substitutions.",
        ),
        "srcs": attr.label_list(
            allow_files = True,
            doc = "List of sources to pass to doxygen",
        ),
        "data": attr.label_list(
            allow_files = True,
            doc = "List of files made available to doxygen when it is running",
        ),
        "env": attr.string_dict(
            allow_empty = True,
            doc = """List of environment variables. The content is location-expanded.
A special DOXYGEN_OUT variable is created which points to a directory where the Doxygen output
should be directed by the Doxyfile.""",
        ),
        "substitutions": attr.string_dict(
            allow_empty = True,
            doc = """List of substitutions to perform in the doxyfile. The content is location-expanded.
                     The following substitutions are implicitely added by the rule:
                     - @@output_dir@@ Path to the output directory
                     - @@src@@ TODO""",
        ),
        "output_groups": attr.string_list_dict(
            allow_empty = True,
            doc = """
                Mappings from output group names to lists of paths contained in
                that group. If a path ends with /, it is declared as a directory,
                otherwise as a file. All paths are relative to the Doxygen output
                directory.
            """,
        ),
    },
    doc = """
Run Doxygen on a set of files.

The expanded Doxyfile will be returned in the DefaultInfo and in a special `doxyfile` output group.
"""
)
