load("@rules_cc//cc:defs.bzl", "cc_library")

def mbed_tls_project(name, config):
    cc_library(
        name = name + "_mbedtls",
        srcs = glob(["library/*.c"]),
        hdrs = glob(["include/**/*.h"]),
        includes = ["include/mbedtls", "include/psa"],
        deps = [config],
        copts = [
            '-DMBEDTLS_CONFIG_FILE=\\"mbedtls_conf.h\\"',
        ],
    )
