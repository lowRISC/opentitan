def _host_libs_impl(repository_ctx):
    # Run ldconfig to find libraries
    result = repository_ctx.execute(["/sbin/ldconfig", "-p"])
    if result.return_code != 0:
        # Try without /sbin
        result = repository_ctx.execute(["ldconfig", "-p"])
        if result.return_code != 0:
            fail("Failed to run ldconfig: " + result.stderr)

    lines = result.stdout.splitlines()
    libs = {
        "libusb-1.0.so": None,
        "libusb-1.0.so.0": None,
        "libftdi1.so": None,
        "libftdi1.so.2": None,
        "libudev.so": None,
        "libudev.so.1": None,
    }

    for line in lines:
        parts = line.strip().split(" => ")
        if len(parts) == 2:
            lib_name_part = parts[0].strip()

            # lib_name_part might look like "libusb-1.0.so.0 (libc6,x86-64)"
            lib_name = lib_name_part.split(" ")[0]
            if lib_name in libs and not libs[lib_name]:
                libs[lib_name] = parts[1].strip()

    # Verify we found all of them
    for name, path in libs.items():
        if not path:
            fail("Could not find library: " + name)

        # Symlink it
        repository_ctx.symlink(path, name)

    # Symlink headers
    repository_ctx.symlink("/usr/include/libusb-1.0/libusb.h", "include/libusb-1.0/libusb.h")
    repository_ctx.symlink("/usr/include/libftdi1/ftdi.h", "include/libftdi1/ftdi.h")
    repository_ctx.symlink("/usr/include/libudev.h", "include/libudev.h")

    repo_path = str(repository_ctx.path("."))

    # Generate libusb-1.0.pc
    repository_ctx.file("libusb-1.0.pc", """
prefix={repo_path}
exec_prefix=${{prefix}}
libdir=${{exec_prefix}}
includedir=${{prefix}}/include

Name: libusb-1.0
Description: C API for USB device access
Version: 1.0.27
Libs: -L${{libdir}} -lusb-1.0
Cflags: -I${{includedir}}/libusb-1.0
""".format(repo_path = repo_path))

    # Generate libftdi1.pc
    repository_ctx.file("libftdi1.pc", """
prefix={repo_path}
exec_prefix=${{prefix}}
libdir=${{exec_prefix}}
includedir=${{prefix}}/include

Name: libftdi1
Description: Library to talk to FTDI chips
Version: 1.5
Requires.private: libusb-1.0
Libs: -L${{libdir}} -lftdi1
Cflags: -I${{includedir}}/libftdi1
""".format(repo_path = repo_path))

    # Generate libudev.pc
    repository_ctx.file("libudev.pc", """
prefix={repo_path}
exec_prefix=${{prefix}}
libdir=${{exec_prefix}}
includedir=${{prefix}}/include

Name: libudev
Description: Library to access udev device information
Version: 250
Libs: -L${{libdir}} -ludev
Cflags: -I${{includedir}}
""".format(repo_path = repo_path))

    # Generate BUILD file
    repository_ctx.file("BUILD", """
package(default_visibility = ["//visibility:public"])

filegroup(
    name = "pc_files",
    srcs = [
        "libusb-1.0.pc",
        "libftdi1.pc",
        "libudev.pc",
    ],
)

cc_import(
    name = "udev_import",
    shared_library = "libudev.so",
)

cc_library(
    name = "udev",
    deps = [":udev_import"],
    data = ["libudev.so.1"],
)

cc_import(
    name = "usb_import",
    shared_library = "libusb-1.0.so",
)

cc_library(
    name = "usb",
    deps = [
        ":usb_import",
        ":udev",
    ],
    data = ["libusb-1.0.so.0"],
)

cc_import(
    name = "ftdi_import",
    shared_library = "libftdi1.so",
)

cc_library(
    name = "ftdi",
    deps = [
        ":ftdi_import",
        ":usb",
    ],
    data = ["libftdi1.so.2"],
)
""")

host_libs = repository_rule(
    implementation = _host_libs_impl,
    local = True,
)
