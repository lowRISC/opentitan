def _openocd_repository_impl(repository_ctx):
    tar_name = "openocd.tgz"
    prefix = "xPacks/openocd/0.10.0-13/"
    repository_ctx.download(
        url = "https://github.com/xpack-dev-tools/openocd-xpack/releases/download/v0.10.0-13/xpack-openocd-0.10.0-13-linux-x64.tgz",
        sha256 = "44fefd65e915e9e697b490eb990b4555424af3b7c166c9e298058dc555039cae",
        output = tar_name,
    )

    # Bazel does not support unicode character targets in download and extract, so extraction happens as a seperate step and files containing unicode characters are removed
    setup_script_template = """
    /bin/tar -zxvf {tar_name}
    # Remove files with unicode characters as bazel doesn't like them
    /bin/rm {prefix}/script/target/к1879xб1я.cfg
    /bin/mv {prefix}/* ./
    /bin/rm -r xPacks {tar_name}
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
    repository_ctx.execute(["./setup.sh"])
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
