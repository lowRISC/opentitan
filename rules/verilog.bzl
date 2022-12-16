# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

def _sv_library_impl(ctx):
    transitive_deps = [dep[DefaultInfo].files for dep in ctx.attr.deps]
    deps = depset(ctx.files.deps, transitive=transitive_deps)
    srcs = ctx.files.srcs
    inputs = depset(srcs, transitive=[deps])
    return [
        DefaultInfo(files = inputs),
    ]

sv_library = rule(
    implementation = _sv_library_impl,
    attrs = {
        "srcs": attr.label_list(
            allow_files = [".sv", ".svh"],
            doc = "SystemVerilog source files",
        ),
        "deps": attr.label_list(
            doc = "Dependencies",
        ),
    },
)

def _sv_list_impl(ctx):
    deps = depset(ctx.files.deps)
    output_file = ctx.actions.declare_file(ctx.label.name + ".svlist")
    ctx.actions.write(
        output = output_file,
        content = "\n".join(
            [f.path for f in deps.to_list()]
        ),
        is_executable = False
    )
    return [
        DefaultInfo(files = depset([output_file])),
    ]


sv_list = rule(
    implementation = _sv_list_impl,
    attrs = {
        "deps": attr.label_list(
            doc = "Dependencies",
        ),
    },
)

def _sv_prim_wrapper_impl(ctx):
    """Build Prim Wrapper for a library

    param[@name]: The library name

    result: `prim_{name}.sv`

    The result module instantiates all possible process libraries.

    e.g) if //**/prim_generic:{name} , //**/prim_somelib:{name} exist,
        the genereated prim_{name}.sv instantiates as below:

        module prim_{name} #(..) (..);
          if (PrimImpl == prim_pkg::ImplSomelib) begin
            prim_somelib_{name} #(..) u_lib (...);
          end else begin
            prim_generic_{name} #(...) u_lib (...);
          end
        endmodule
    """
    wrapper = ctx.actions.declare_file("prim_{}.sv".format(ctx.label.name))
    deps = ctx.files.deps
    print("files:", deps)

    # TODO: Get the possible techlib (generic, xilinx, ...) and give the list +
    # file list as arguments in the form of:
    #  -l lib1.sv -l lib2.sv
    args = ctx.actions.args()
    for f in deps:
        args.add("--lib", f)
    ctx.actions.run(
        outputs = [wrapper],
        inputs = deps,
        arguments = [
            "-o",
            wrapper.path,
            args,
        ],
        executable = ctx.executable._primgen,
    )

    return [
        DefaultInfo(files = depset([wrapper])),
    ]

sv_prim_wrapper = rule(
    implementation = _sv_prim_wrapper_impl,
    attrs = {
        "_primgen": attr.label(
            doc = "Primgen executable",
            executable = True,
            default = "//util/design/primgen:primgen",
            cfg = "exec",
        ),
        "deps": attr.label_list(
            doc = "Dependent libraries",
            allow_files = [".sv"],
        ),
    },
)
