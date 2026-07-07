# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

"""Repository rule for locating host libraries using pkg-config.

This rule queries the host system to find required libraries, symlinks their
headers and library files into the repository, and generates relocatable
pkg-config (.pc) files pointing to these symlinks.
"""

def _get_pkg_var(repository_ctx, pkg_config, pkg_name, var_name):
    """Queries pkg-config for a specific variable (e.g., includedir, libdir)."""
    res = repository_ctx.execute([pkg_config, "--variable=" + var_name, pkg_name])
    if res.return_code != 0:
        fail("Failed to get {} for {}: {}".format(var_name, pkg_name, res.stderr))
    return res.stdout.strip()

def _get_pkg_flags(repository_ctx, pkg_config, pkg_name, flag):
    """Queries pkg-config for compiler or linker flags (e.g., --libs, --cflags)."""
    res = repository_ctx.execute([pkg_config, flag, pkg_name])
    if res.return_code != 0:
        fail("Failed to get flags {} for {}: {}".format(flag, pkg_name, res.stderr))
    return res.stdout.strip()

def _extract_l_flags(libs_flags):
    """Removes -L flags from pkg-config output.

    We strip host library search paths (-L/usr/lib...) to prevent pulling in
    unwanted host libraries during downstream compilation. We rely on Bazel's
    dependency management instead.
    """
    tokens = libs_flags.split(" ")
    kept = []
    for t in tokens:
        if t and not t.startswith("-L"):
            kept.append(t)
    return " ".join(kept)

def _generate_build_file(repository_ctx, status, config, pc_files):
    """Generates the BUILD file for the external repository."""
    build_content = "package(default_visibility = [\"//visibility:public\"])\n\n"

    # pc_files filegroup
    build_content += "filegroup(\n"
    build_content += "    name = \"pc_files\",\n"
    build_content += "    srcs = [\n"
    for pc in pc_files:
        build_content += "        \"{}\",\n".format(pc)
    build_content += "    ],\n"
    build_content += ")\n\n"

    for pc in pc_files:
        build_content += "exports_files([\"{}\"])\n\n".format(pc)

    for name, lib_config in config.items():
        if not status[name]:
            continue

        main_lib = None
        data_libs = []
        for lib in lib_config["libs"]:
            if lib.endswith(".so"):
                main_lib = lib
            else:
                data_libs.append(lib)

        if not main_lib:
            main_lib = lib_config["libs"][0]
            data_libs = lib_config["libs"][1:]

        import_name = name + "_import"
        build_content += "cc_import(\n"
        build_content += "    name = \"{}\",\n".format(import_name)
        build_content += "    shared_library = \"{}\",\n".format(main_lib)
        build_content += ")\n\n"

        build_content += "cc_library(\n"
        build_content += "    name = \"{}\",\n".format(name)
        build_content += "    deps = [\n"
        build_content += "        \":{}\",\n".format(import_name)
        for dep in lib_config.get("deps", []):
            if status.get(dep, False):
                build_content += "        \":{}\",\n".format(dep)
        build_content += "    ],\n"
        if data_libs:
            build_content += "    data = [\n"
            for lib in data_libs:
                build_content += "        \"{}\",\n".format(lib)
            build_content += "    ],\n"
        build_content += ")\n\n"

    repository_ctx.file("BUILD", build_content)

def _host_libs_impl(repository_ctx):
    """Implementation of the host_libs repository rule."""
    config_str = repository_ctx.attr.config
    config = json.decode(config_str)

    pkg_config = repository_ctx.which("pkg-config")
    if not pkg_config:
        # Write all false status
        status_content = ""
        for name in config.keys():
            status_content += "HAS_{} = False\n".format(name.upper())
        repository_ctx.file("status.bzl", status_content)
        repository_ctx.file("BUILD", "package(default_visibility = [\"//visibility:public\"])\nfilegroup(name = \"pc_files\", srcs = [])\n")
        return

    status = {}
    repo_path = str(repository_ctx.path("."))
    pc_files = []

    for name, lib_config in config.items():
        pkg_name = lib_config["pkg_name"]

        res = repository_ctx.execute([pkg_config, "--exists", pkg_name])
        if res.return_code != 0:
            status[name] = False
            continue

        status[name] = True

        includedir = _get_pkg_var(repository_ctx, pkg_config, pkg_name, "includedir")
        libdir = _get_pkg_var(repository_ctx, pkg_config, pkg_name, "libdir")

        res = repository_ctx.execute([pkg_config, "--modversion", pkg_name])
        version = res.stdout.strip() if res.return_code == 0 else "0.0.0"

        # Symlink headers
        for header in lib_config["headers"]:
            src = includedir + "/" + header
            dest = "include/" + header
            repository_ctx.symlink(src, dest)

        # Symlink libs
        for lib in lib_config["libs"]:
            src = libdir + "/" + lib
            repository_ctx.symlink(src, lib)

        # Generate .pc file
        libs_flags = _get_pkg_flags(repository_ctx, pkg_config, pkg_name, "--libs")
        cflags_flags = _get_pkg_flags(repository_ctx, pkg_config, pkg_name, "--cflags")

        libs_flags = libs_flags.replace(libdir, "${libdir}")
        cflags_flags = cflags_flags.replace(includedir, "${includedir}")

        pc_filename = pkg_name + ".pc"
        repository_ctx.file(pc_filename, """prefix={repo_path}
exec_prefix=${{prefix}}
libdir=${{exec_prefix}}
includedir=${{prefix}}/include

Name: {name}
Description: Host library {name}
Version: {version}
Libs: -L${{libdir}} {libs_flags}
Cflags: {cflags_flags}
""".format(
            repo_path = repo_path,
            name = name,
            version = version,
            libs_flags = _extract_l_flags(libs_flags),
            cflags_flags = cflags_flags,
        ))
        pc_files.append(pc_filename)

    status_content = ""
    for name, val in status.items():
        status_content += "HAS_{} = {}\n".format(name.upper(), str(val))
    repository_ctx.file("status.bzl", status_content)

    _generate_build_file(repository_ctx, status, config, pc_files)

DEFAULT_CONFIG = {
    "usb": {
        "pkg_name": "libusb-1.0",
        "headers": ["libusb-1.0/libusb.h"],
        "libs": ["libusb-1.0.so", "libusb-1.0.so.0"],
        "deps": ["udev"],
    },
    "ftdi": {
        "pkg_name": "libftdi1",
        "headers": ["libftdi1/ftdi.h"],
        "libs": ["libftdi1.so", "libftdi1.so.2"],
        "deps": ["usb"],
    },
    "udev": {
        "pkg_name": "libudev",
        "headers": ["libudev.h"],
        "libs": ["libudev.so", "libudev.so.1"],
        "deps": [],
    },
}

host_libs = repository_rule(
    doc = """Locates host libraries and generates symlinks and relocatable .pc files.

    Generates:
    - BUILD: Defines cc_library targets for found host libraries.
    - status.bzl: Exports HAS_XYZ booleans indicating detection status.
    - <lib>.pc: Relocatable pkg-config files pointing to the symlinked resources.
    """,
    implementation = _host_libs_impl,
    local = True,
    attrs = {
        "config": attr.string(
            doc = "JSON-encoded configuration specifying libraries, headers, and dependencies.",
            default = json.encode(DEFAULT_CONFIG),
        ),
    },
)
