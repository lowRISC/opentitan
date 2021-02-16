def _toolchain_upstream_repository_impl(rctx):
    rctx.file("BUILD", """
package(default_visibility = ["//visibility:public"])
load("@bazel_embedded//toolchains/tools/include_tools:defs.bzl","cc_injected_toolchain_header_library","cc_polyfill_toolchain_library")
cc_polyfill_toolchain_library(
    name = "polyfill",
)

cc_injected_toolchain_header_library(
    name = "injected_headers",
)
""")

toolchain_upstream_repository = repository_rule(
    _toolchain_upstream_repository_impl,
)

def toolchain_upstream_deps():
    toolchain_upstream_repository(
        name = "bazel_embedded_upstream_toolchain",
    )
