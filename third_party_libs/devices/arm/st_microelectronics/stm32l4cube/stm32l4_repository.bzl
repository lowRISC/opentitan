load(":stm32l4_defs.bzl", "STM32_DEFINES")

VERSIONS = {
    # TODO: Fetch these to determine sha sums when internet is better
    "v1.15.1": {
        "commit": "285336eeffa12f9cee3a1784a6b60744bd43c0d9",
        "sha256": "",
    },
    # TODO: Fetch these to determine sha sums when internet is better
    "v1.15.0": {
        "commit": "fd2610d0f313d46c8e9ef33e10dcbd2b1dd7fdff",
        "sha256": "",
    },
    # TODO: Fetch these to determine sha sums when internet is better
    "v1.14.0": {
        "commit": "f6877af03b5c8b666b3443f5295cf95ec9c0b15d",
        "sha256": "",
    },
}

def _stm32h7xx_repository_impl(rctx):
    REPOSITORY_NAME = "STM32CubeH7"
    BASE_URL = "https://github.com/STMicroelectronics/" + REPOSITORY_NAME + "/archive/"

    version_info = VERSIONS[rctx.attr.version]
    rctx.download_and_extract(
        url = BASE_URL + version_info["commit"] + ".zip",
        stripPrefix = REPOSITORY_NAME + "-" + version_info["commit"],
        sha256 = version_info["sha256"],
    )
    rctx.symlink(Label("//devices/arm/st_microelectronics/stm32l4cube:stm32l4_defs.bzl"), "stm32l4_defs.bzl")
    target_template = """
stm32l4_project(
    name = "{name}",
    config = "{config}",
)
"""
    startup_template = """
cc_library(
    name = "startup_{device}",
    srcs = ["Drivers/CMSIS/Device/ST/STM32L4xx/Source/Templates/gcc/startup_{device}.s"],
    alwayslink = True,
    tags = ["manual"],
)
"""
    startup_targets = [startup_template.format(device = device) for device in STM32_DEFINES.keys()]
    startup_targets_str = "\n".join(startup_targets)
    targets = [target_template.format(config = config, name = name) for name, config in rctx.attr.project_configs.items()]
    targets_str = "\n".join(targets)
    rctx.file("BUILD", """
package(default_visibility = ["//visibility:public"])
exports_files(glob(["**/*.s"]))
load(":stm32h7_defs.bzl","stm32h7_project")
""" + targets_str + startup_targets_str)

stm32l4_repository_simple = repository_rule(
    implementation = _stm32h7xx_repository_impl,
    attrs = {
        "version": attr.string(
            doc = "Release version of repository",
            default = "v1.15.1",
            values = VERSIONS.keys(),
        ),
        "project_configs": attr.string_dict(
            doc = "The key as the named prefix for this project and the value as the Label for your projects config cc_library",
            mandatory = True,
        ),
    },
)

def stm32l4_repository(project_configs, version = "v1.15.1"):
    stm32l4_repository_simple(name = "stm32h7cube", project_configs = project_configs, version = version)
