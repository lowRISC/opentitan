def _get_platform_specific_config(os_name):
    _PLATFORM_SPECIFIC_CONFIGS = {
        "mac os x": {
            "sha256": "30917a5c6f60fcd7df82b41dcec8ab7d86f0cea3caeaf98b965b901c10a60b39",
            "prefix": "xpack-openocd-0.10.0-14",
            "url": "https://github.com/xpack-dev-tools/openocd-xpack/releases/download/v0.10.0-14/xpack-openocd-0.10.0-14-darwin-x64.tar.gz",
        },
        "linux": {
            "sha256": "185c070f9729cf38dca08686c2905561c07a63c563e5bc7a70e045f2a1865c11",
            "prefix": "xpack-openocd-0.10.0-14",
            "url": "https://github.com/xpack-dev-tools/openocd-xpack/releases/download/v0.10.0-14/xpack-openocd-0.10.0-14-linux-x64.tar.gz",
        },
    }
    if os_name not in _PLATFORM_SPECIFIC_CONFIGS.keys():
        fail("OS configuration not available for:", os_name)
    return _PLATFORM_SPECIFIC_CONFIGS[os_name]

def _openocd_repository_impl(repository_ctx):
    tar_name = "openocd.tgz"

    config = _get_platform_specific_config(repository_ctx.os.name)
    prefix = config["prefix"]
    repository_ctx.download(
        url = config["url"],
        sha256 = config["sha256"],
        output = tar_name,
    )

    # Bazel does not support unicode character targets in download and extract, so extraction happens as a seperate step and files containing unicode characters are removed
    setup_script_template = """
    set -eux pipefail
    tar -zxvf {tar_name}
    # Remove files with unicode characters as bazel doesn't like them
    /bin/mv {prefix}/* ./
    /bin/rm -r  {tar_name}
    """

    # Adds variables to script
    setup_script = setup_script_template.format(
        tar_name = tar_name,
        prefix = prefix,
    )

    # Create setup shell script in current directory
    repository_ctx.file(
        "setup.sh",
        content = setup_script,
        executable = True,
    )

    # Execute Setup script
    result = repository_ctx.execute(["./setup.sh"])
    if result.return_code != 0:
        fail("Setup failed\n STDERR: %s\n STDOUT: %s\n" % (result.stderr, result.stdout))

    repository_ctx.symlink("bin/openocd", "openocd")

    repository_ctx.file(
        "BUILD",
        content = """
package(default_visibility = ["//visibility:public"])
exports_files(["openocd"])
""",
    )

openocd_repository = repository_rule(
    _openocd_repository_impl,
)

def openocd_deps():
    """ openocd_deps fetchs openocd from the xpack repositories
    """
    openocd_repository(name = "com_openocd")
