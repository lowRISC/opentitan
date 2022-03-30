load("@rules_python//python:defs.bzl", "py_binary")
load("@ot_python_deps//:requirements.bzl", "requirement")

package(default_visibility = ["//visibility:public"])

py_binary(
    name = "extract_sw_logs_db",
    srcs = ["extract_sw_logs.py"],
    main = "extract_sw_logs.py",
    deps = [
        requirement("pyelftools"),
    ],
)
