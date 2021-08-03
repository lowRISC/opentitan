load("//toolchains/compilers/lowrisc_toolchain_rv32imc/impl:lowrisc_toolchain_rv32imc_versions.bzl", "TOOLCHAIN_VERSIONS", "get_platform_specific_config")
load("//toolchains/tools/include_tools:include_tools.bzl", "include_tools")

def _com_lowrisc_toolchain_rv32imc_repository_impl(repository_ctx):
    version = repository_ctx.attr.version
    remote_toolchain_info = get_platform_specific_config(version, repository_ctx.os.name)

    repository_ctx.download_and_extract(
        url = remote_toolchain_info["remote_compiler"]["url"],
        sha256 = remote_toolchain_info["remote_compiler"]["sha256"],
        stripPrefix = remote_toolchain_info["remote_compiler"]["strip_prefix"],
    )
    postfix = ""
    if "windows" in repository_ctx.os.name:
        os = "windows"
        postfix = ".exe"
    elif "mac" in repository_ctx.os.name:
        os = "unix"
    else:
        os = "linux"
    response = repository_ctx.execute(include_tools.ShellCommand(
        "bin/riscv32-unknown-elf-cpp" + postfix,
        [
            "-specs=nano.specs",
            "-specs=nosys.specs",
        ],
        os,
    ))
    include_paths = include_tools.ProccessResponse(response.stderr)
    include_flags = ["-isystem" + path for path in include_paths]
    include_bazel_template_input = include_tools.CommandLineToTemplateString(include_flags)
    include_paths_template_input = include_tools.CommandLineToTemplateString(include_paths)
    repository_ctx.file(
        "defs.bzl",
        """
SYSTEM_INCLUDE_COMMAND_LINE = {}
SYSTEM_INCLUDE_PATHS = {}
""".format(include_bazel_template_input, include_paths_template_input),
    )

    repository_ctx.file(
        "BUILD",
        """
filegroup(
    name = "all",
    srcs = glob(["**/*"], exclude=["**/*.html", "**/*.pdf"]),
    visibility = ['//visibility:public'],
)
exports_files(
    glob(["bin/**"])
)
""",
    )

lowrisc_toolchain_rv32imc_repository = repository_rule(
    _com_lowrisc_toolchain_rv32imc_repository_impl,
    attrs = {
        "version": attr.string(
            default = "9",
            doc = "GCC version, version 9 currently only version supported",
            values = TOOLCHAIN_VERSIONS.keys(),
        ),
    },
)

def lowrisc_toolchain_rv32imc_compiler():
    lowrisc_toolchain_rv32imc_repository(
        name = "com_lowrisc_toolchain_rv32imc_compiler",
    )
