load(":stm32h7_defs.bzl", "STM32_DEFINES")

VERSIONS = {
    "v1.7.0": {
        "commit": "79196b09acfb720589f58e93ccf956401b18a191",
        "sha256": "51ce7f158d9acbd28b59bef8a48b5b1921b10a63a054fdcb9776a83d876f1dad",
    },
    # TODO: Fetch these to determine sha sums when internet is better
    "v1.6.0": {
        "commit": "3d3ffbe6e15fc7e4d8a4d275e9fb3a334e31c8a3",
        "sha256": "",
    },
    # TODO: Fetch these to determine sha sums when internet is better
    "v1.5.0": {
        "commit": "e261d820b398846a94f22f4aeb32d86c29546efb",
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
    rctx.symlink(Label("//devices/arm/st_microelectronics/stm32h7cube:stm32h7_defs.bzl"), "stm32h7_defs.bzl")
    target_template = """
stm32h7_project(
    name = "{name}",
    config = "{config}",
)
"""
    startup_template = """
cc_library(
    name = "startup_{device}",
    srcs = ["Drivers/CMSIS/Device/ST/STM32H7xx/Source/Templates/gcc/startup_{device}.s"],
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

stm32h7_repository_simple = repository_rule(
    implementation = _stm32h7xx_repository_impl,
    attrs = {
        "version": attr.string(
            doc = "Release version of repository",
            default = "v1.7.0",
            values = VERSIONS.keys(),
        ),
        "project_configs": attr.string_dict(
            doc = "The key as the named prefix for this project and the value as the Label for your projects config cc_library",
            mandatory = True,
        ),
    },
)

def stm32h7_repository(project_configs, version = "v1.7.0"):
    stm32h7_repository_simple(name = "stm32h7cube", project_configs = project_configs, version = version)
