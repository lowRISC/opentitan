def _cc_injected_toolchain_header_library_impl(ctx):
    hdrs = ctx.files.hdrs
    transitive_cc_infos = [dep[CcInfo] for dep in ctx.attr.deps]
    compilation_ctx = \
        cc_common.create_compilation_context(headers = depset(hdrs))
    info = cc_common.merge_cc_infos(
        cc_infos = transitive_cc_infos +
                   [CcInfo(compilation_context = compilation_ctx)],
    )
    return [info, DefaultInfo(files = depset(hdrs))]

cc_injected_toolchain_header_library = rule(
    _cc_injected_toolchain_header_library_impl,
    attrs = {
        "hdrs": attr.label_list(
            doc = "A list of headers to be included into a toolchain implicitly\
             using -include",
            allow_files = True,
        ),
        "deps": attr.label_list(
            doc = "list of injected header libraries that this target depends on",
            providers = [CcInfo],
        ),
    },
    provides = [CcInfo],
)

def _normalise_include(ctx, inc):
    root_str = ""
    if ctx.label.workspace_root:
        root_str = ctx.label.workspace_root + "/"
    return root_str + ctx.label.package + "/" + inc

def _cc_toolchain_header_polyfill_library_impl(ctx):
    hdrs = ctx.files.hdrs
    system_includes = \
        [_normalise_include(ctx, inc) for inc in ctx.attr.system_includes] + \
        [ctx.label.workspace_root]
    transitive_cc_infos = [dep[CcInfo] for dep in ctx.attr.deps]
    compilation_ctx = cc_common.create_compilation_context(
        headers = depset(hdrs),
        system_includes = depset(system_includes),
    )
    info = cc_common.merge_cc_infos(
        cc_infos = transitive_cc_infos +
                   [CcInfo(compilation_context = compilation_ctx)],
    )
    return [
        info,
        DefaultInfo(files =
                        depset(hdrs, transitive = [info.compilation_context.headers])),
    ]

cc_polyfill_toolchain_library = rule(
    _cc_toolchain_header_polyfill_library_impl,
    attrs = {
        "hdrs": attr.label_list(
            doc = "A list of headers to be included into the toolchains system \
            libraries",
            allow_files = True,
        ),
        "system_includes": attr.string_list(
            doc = "A list of directories to be included when the toolchain \
            searches for headers",
        ),
        "deps": attr.label_list(
            doc = "list of injected header libraries that this target depends\
             on",
            providers = [CcInfo],
        ),
    },
)
