def register_platforms():
    native.register_execution_platforms("@local_config_platform//:host","@bazel_embedded//platforms:all")
