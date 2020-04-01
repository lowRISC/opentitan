# Config target must provide mbedtls_conf.h
cc_library(
    name = "minimal_mbedtls_conf",
    hdrs = ["mbedtls_conf.h"],
    strip_include_prefix = ".",
    visibility = ["//visibility:public"],
)

CONFIG_NAME = "minimal"

cc_library(
    name = "rsa_sign",
    srcs = ["rsa_sign.c"],
    deps = ["@com_mbedtls//:%s_mbedtls" % CONFIG_NAME],
)
