
_PLATFORM_SPECIFIC_CONFIGS_9 = {
    "linux": {
        "full_version": "9.2.0",
        "remote_compiler": {
            "url": "https://github.com/lowRISC/lowrisc-toolchains/releases/download/20210412-1/lowrisc-toolchain-rv32imc-20210412-1.tar.xz",
            "sha256": "b339d241e9b3cf60d4f81bfdd9da102c4f3889df615e8b6d82e5fba43d36162a",
            "strip_prefix": "lowrisc-toolchain-rv32imc-20210412-1",
        },
    },
}

TOOLCHAIN_VERSIONS = {
    "9": _PLATFORM_SPECIFIC_CONFIGS_9,
}

def get_platform_specific_config(version, os_name):
    if version not in TOOLCHAIN_VERSIONS:
        fail("Toolchain configuration not available for version: ", version)
    if os_name not in TOOLCHAIN_VERSIONS[version].keys():
        fail("OS configuration not available for: {}".format(os_name))
    return TOOLCHAIN_VERSIONS[version][os_name]
