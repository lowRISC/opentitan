load("@rules_python//python:defs.bzl", "py_test", "py_library", "py_binary")

licenses(["notice"])

py_library(
    name = "verible_verilog_syntax_py",
    srcs = ["verible_verilog_syntax.py"],
    srcs_version = "PY3",
    imports = ["."],
    data = ["//verilog/tools/syntax:verible-verilog-syntax"],
    deps = [
        "@python_anytree//:anytree",
        "//third_party/py/dataclasses",
    ],
)

py_test(
    name = "verible_verilog_syntax_py_test",
    size = "small",
    srcs = ["verible_verilog_syntax_test.py"],
    srcs_version = "PY3",
    python_version = "PY3",
    main = "verible_verilog_syntax_test.py",
    deps = [":verible_verilog_syntax_py"],
    data = ["//verilog/tools/syntax:verible-verilog-syntax"],
    args = ["$(location //verilog/tools/syntax:verible-verilog-syntax)"],
)

py_binary(
    name = "print_modules",
    srcs = ["print_modules.py"],
    srcs_version = "PY3",
    python_version = "PY3",
    main = "print_modules.py",
    deps = [
         ":verible_verilog_syntax_py",
         "@python_anytree//:anytree",
    ],
    data = ["//verilog/tools/syntax:verible-verilog-syntax"],
    args = ["$(location //verilog/tools/syntax:verible-verilog-syntax)"],
)

py_binary(
    name = "print_tree",
    srcs = ["print_tree.py"],
    srcs_version = "PY3",
    python_version = "PY3",
    main = "print_tree.py",
    deps = [
         ":verible_verilog_syntax_py",
         "@python_anytree//:anytree",
    ],
    data = ["//verilog/tools/syntax:verible-verilog-syntax"],
    args = ["$(location //verilog/tools/syntax:verible-verilog-syntax)"],
)
