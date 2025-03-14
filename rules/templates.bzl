# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("@rules_python//python:defs.bzl", "py_binary")
load("@ot_python_deps//:requirements.bzl", "requirement")
load("//rules/opentitan:hw.bzl", "OpenTitanTopInfo")

def _find_label(ctx, label):
    label = Label(label)
    for (dep, dep_label) in ctx.attr.data.items():
        # Here we need to use a trick: if the dep was given an alias, Bazel will
        # resolve the target to the pointed target and so its label will be the
        # resolve label, not the original one. For example, if //hw/top:top_desc
        # points to //hw/top:top_earlgrey_desc then the target's label will be
        # //hw/top:top_earlgrey_desc. We avoid this issues by also passing the
        # original label string in the macro.
        if Label(dep_label) == label:
            return dep
    fail("unknown label '{}': make sure this label is listed in the deps".format(label))

def _get_path(object, pathstr):
    for item in pathstr.split("."):
        if type(object) == "dict":
            if not item in object:
                fail("cannot find path {} in {}".format(pathstr, item))
            object = object[item]
        else:
            if not hasattr(object, item):
                fail("cannot find path {} in {}".format(pathstr, item))
            object = getattr(object, item)
    return object

def _expand_func(ctx, args, extra_locations):
    if len(args) == 0:
        fail("invalid empty call $()")
    func = args[0]
    if func == "topinfo":
        if len(args) != 3:
            fail("topinfo requires exactly two arguments: a label to the top description and a path")
        top_desc = _find_label(ctx, args[1])
        res = _get_path(top_desc[OpenTitanTopInfo], args[2])

        # If the result is a Target, expand to a label
        if type(res) == "Target":
            return str(res.label), [res]
        elif type(res) == "File":
            return res.path, []
        else:
            return str(res), []
    if func in ["location", "locations"]:
        return ctx.expand_location("$(" + " ".join(args) + ")", extra_locations), []

    fail("call to unknown function '{}'".format(func))

def _split_on_spaces(input):
    output = []
    for _ in range(len(input)):
        input = input.lstrip()
        if input == "":
            break
        res = input.split(" ", 1)
        output.append(res[0])
        if len(res) == 2:
            input = res[1]
        else:
            break
    return output

def _expand_funcs(ctx, input):
    extra_locations = []
    for _ in range(len(input)):
        # Very naive parsing: find a $(...) substring. To make sure that this
        # substring does not itself contain a nested call, find the last occurence.
        before, sep, after = input.rpartition("$(")
        if sep == "":
            break
        call, paren, after = after.partition(")")
        if paren == "":
            break
        args = _split_on_spaces(call)
        call_res, new_locs = _expand_func(ctx, args, extra_locations)
        extra_locations.extend(new_locs)
        input = before + call_res + after

    return input, extra_locations

def _render_template_impl(ctx):
    # See documentation for how the filename is constructed.
    filename = ctx.attr.filename
    if filename == "":
        filename = ctx.label.name
        tplname = ctx.file.template.basename
        if tplname.endswith(".tpl"):
            tplname = tplname.removesuffix(".tpl")
        _, dot, ext = tplname.partition(".")
        if dot == ".":
            filename += dot + ext
    output = ctx.actions.declare_file(filename)

    arguments = [
        "-o",
        output.path,
        ctx.file.template.path,
    ]

    # Expand all locations within the variables.
    extra_locations = []
    for (var, val) in ctx.attr.variables.items():
        val, new_locs = _expand_funcs(ctx, val)
        extra_locations.extend(new_locs)
        arguments.extend([
            "--var",
            "{}={}".format(var, val),
        ])

    # Collect data files.
    data_files = []
    for dep in ctx.attr.data.keys() + extra_locations + [ctx.attr.template]:
        data_files.append(dep[DefaultInfo].files)

    ctx.actions.run(
        outputs = [output],
        inputs = depset(transitive = data_files),
        arguments = arguments,
        executable = ctx.executable.render_tool,
    )

    return [
        DefaultInfo(files = depset([output])),
    ]

_render_template = rule(
    implementation = _render_template_impl,
    doc = "See mako_template macro",
    attrs = {
        "template": attr.label(
            mandatory = True,
            allow_single_file = True,
            doc = "Template to render",
        ),
        "data": attr.label_keyed_string_dict(
            default = {},
            doc = "List of data dependencies, in the format Label() -> string. The string is necessary to resolve aliases.",
        ),
        "variables": attr.string_dict(
            doc = "Dictionary of variables",
        ),
        "filename": attr.string(
            default = "",
            doc = "Override the default filename of the rendered template",
        ),
        "render_tool": attr.label(
            mandatory = True,
            executable = True,
            cfg = "host",
            doc = "Tool used to render the template",
        ),
    },
)

def render_template(
        name,
        template,
        render_tool,
        data = [],
        variables = {},
        filename = "",
        target_compatible_with = None):
    """
    Render a template.

    This rule will render a template file using a given tool, and optionally
    provide variables to the rendering tool so that they can be used within
    the template. The template and/or rendering tool can use any file listed
    in the `data` argument.

    **Filename**
    Unless specified using the `filename` attribute, the output file name is
    constructed as `<name><ext>` where `<name>` is the target name and
    `ext` is the extension of the template (without `.tpl` if the template
    ends with `.tpl`).

    **Variables**
    Variables can be passed to the rendering tool by passing a dictionary of
    strings. The variable names are kept as-is while the content of each variable
    is subject to expansions (see below). The variables are passed to the
    rendering tool on the command-line using `--var <name>=<value>`
    (two arguments).
    Example:
    ```
    variables = {
      "some_var": "some string",
      "other_var": "$(location //some/label)",
    }
    ```

    **Expansion in variables**
    The rule will perform the usual location expansion using [1]. Furthermore,
    the rule will try to expand any function call of the form:
    ```
    $(fnname arg1 arg2...)
    ```
    Currently, the following functions are recognized:
    - location, locations: `$(location <label>)`
        Expands to the path(s) of the output file of `<label>`, using [1].
        The <label> must be listed in the `data` attribute of the rule.
        Example:
          $(location //hw/top:top_ld)
    - topinfo: `$(topinfo <label> <path>)`
        Expands to the value in the `OpenTitanTopInfo` provider of the <label>,
        at the path indicated by <path>. More precisely, the rule will resolve
        <label>, which must be listed in the `data` attribute, and find its
        `OpenTitanTopInfo` provider. It will then find the field that corresponds
        to the <path> which must be encoded in the form `field[.field]...`.
        Each field will be resolved recursively, either using `getattr` for structs
        or `[]` for dictionaries. The result of the expansion then depends on the
        type of the value:
        * `Target`: expanded to its label,
        * `File`: expanded to the path to the file,
        * anything else: converted to string (or error if not possible).

        Example:
        * `$(topinfo //hw/top:top_desc hjson)`
          will expand to `hw/top_earlgrey/data/autogen/top_earlgrey.gen.hjson`
          (for earlgrey) because //hw/top:top_desc is an alias to the top's
          description and the `hjson` field of the top info provider is
          a File.
        * `$(topinfo //hw/top:top_desc ip_map.uart.hjson)`
          will expand to `@@//hw/ip/uart/data:uart.hjson` because the `ip_map`
          field of the info provider is a dictionary mapping IP names to a struct
          whose `hjson` field is a Target.

    Nested expansion is supported, for example if a $(topinfo) expands to a label,
    then a further location expansion might be necessary:
      $(location $(topinfo //hw/top:top_desc ip_map.uart.hjson))


    [1] https://bazel.build/rules/lib/builtins/ctx#expand_location


    Args:
      name (string): Target name
      template (label): Label of template.
      data (label array): List of data dependencies.
      variables (string dict): Dictionary of variables, subject to expansion.
      filename (string): Name of the output file (optional)
      target_compatible_with (string list): List of target constraints.
    """
    _render_template(
        name = name,
        template = template,
        data = {
            dep: str(dep)
            for dep in data
        },
        variables = variables,
        filename = filename,
        render_tool = render_tool,
        target_compatible_with = target_compatible_with,
    )

def mako_template(
        name,
        template,
        deps = [],
        data = [],
        variables = {},
        filename = "",
        target_compatible_with = None):
    """
    Render a mako template.

    This macro uses `render_template` to render a Mako template.
    The variables are available to the template as global variables.
    In addition to the `render_template` rule, this macro supports
    an extra `deps` argument for python runtime dependencies used by
    the template such as python libraries or packages.

    NOTE In addition to the target created by `render_template`,
    this macro will create an extra `<name>_render_tool` target
    for technical reasons.

    Extra args:
      deps (label array): list of python runtime dependencies.

    Example:
    ```py
    mako_template(
      name = "some_target",
      template = "some_template.tpl",
      data = {
        "some_var": "variable content",
      },
      deps = [
        "//label/to/some/python/library",
        requirement("hjson"),
      ],
    )
    ```
    """

    # Here there is a bit of a difficulty: we want the `deps` to correctly
    # setup the python environment (e.g. set the python path) but emulating
    # this logic is quite difficult. Therefore we create a python binary
    # specifically for each rendering job and pass all the dependencies
    # at this point so that rules_python can take care of this. This requires
    # the mako rendering script to be just a file, not a python library.
    render_tool = name + "_render_tool"
    py_binary(
        name = render_tool,
        main = "render_mako.py",
        srcs = ["//rules/scripts:render_mako.py"],
        deps = deps + [requirement("mako")],
    )

    render_template(
        name = name,
        template = template,
        render_tool = ":{}".format(render_tool),
        data = data,
        variables = variables,
        filename = filename,
        target_compatible_with = target_compatible_with,
    )
