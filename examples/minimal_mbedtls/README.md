# Minimal mbedtls project
This is a minimal project that shows how to setup a dependency on mbedtls

## Config
mbedtls requires a config header file in order to provide this you may provide one or more configs, when setting up mbed.

Your WORKSPACE file should look something like this;

```python
workspace(name = "minimal_mbedtls")

load("@bazel_tools//tools/build_defs/repo:git.bzl", "git_repository")

git_repository(
    name = "bazel_embedded",
    commit = "c72c4fa0de5ce3ddc826ad23f3770e4134165ca3",
    remote = "git@github.com:silvergasp/bazel-embedded.git",
    shallow_since = "1585022166 +0800",
)

load("@bazel_embedded//:bazel_embedded_deps.bzl", "bazel_embedded_deps")

bazel_embedded_deps()

load("@bazel_embedded//third_party_libs/crypto/mbedtls:mbedtls_repository.bzl", "mbedtls_repository")

mbedtls_repository(
    project_configs = {
        # Multiple configs allowed, in the form "{config_name}": "@{some_repo}//{config_cc_library_target}"
        "minimal": "@minimal_mbedtls//:minimal_mbedtls_conf",
        "some_other_config": "@minimal_mbedtls//:some_other_config",
    },
)

```

With the above example WORKSPACE file you may have the following BUILD file that depends on a particular config of mbedtls.

```python
# Config target must provide mbedtls_conf.h
cc_library(
    name = "minimal_mbedtls_conf",
    hdrs = ["mbedtls_conf.h"],
    strip_include_prefix = ".",
    visibility = ["//visibility:public"],
)

# This must match one of the config names referenced in your mbedtls_repository project_configs attribute
CONFIG_NAME = "minimal"

cc_library(
    name = "rsa_sign",
    srcs = ["rsa_sign.c"],
    # Depending on your configured mbedtls library
    deps = ["@com_mbedtls//:%s_mbedtls" % CONFIG_NAME],
)

```