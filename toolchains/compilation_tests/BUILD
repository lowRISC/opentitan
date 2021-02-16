load("@rules_cc//cc:defs.bzl", "cc_binary", "cc_test")

cc_binary(
    name = "compilation_test_c",
    srcs = ["compilation_test.c"],
    visibility = ["//visibility:public"],
)

cc_binary(
    name = "compilation_test_cc",
    srcs = ["compilation_test.cc"],
    visibility = ["//visibility:public"],
)

cc_test(
    name = "host_targetted_compilation_test_cc",
    srcs = ["host_targetted_compilation_test.cc"],
    target_compatible_with = ["@platforms//cpu:x86_64"],
)
