load("@rules_cc//cc:defs.bzl", "cc_library")

def mbedtls_project(name, config):
    cc_library(
        name = name + "_mbedtls",
        srcs = native.glob(["library/*.c"]),
        hdrs = native.glob(["include/**/*.h"]),
        includes = ["include"],
        deps = [config],
        copts = [
            '-DMBEDTLS_CONFIG_FILE=\\"mbedtls_conf.h\\"',
        ],
    )
