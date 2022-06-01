"""
@generated
cargo-raze generated Bazel file.

DO NOT EDIT! Replaced on runs of cargo-raze
"""

load("@bazel_tools//tools/build_defs/repo:git.bzl", "new_git_repository")  # buildifier: disable=load
load("@bazel_tools//tools/build_defs/repo:http.bzl", "http_archive")  # buildifier: disable=load
load("@bazel_tools//tools/build_defs/repo:utils.bzl", "maybe")  # buildifier: disable=load

# EXPERIMENTAL -- MAY CHANGE AT ANY TIME: A mapping of package names to a set of normal dependencies for the Rust targets of that package.
_DEPENDENCIES = {
    "third_party/tock/crates": {
        "earlgrey-cw310": "@raze__earlgrey_cw310__0_1_0//:earlgrey_cw310",
        "libtock2": "@raze__libtock2__0_1_0//:libtock2",
    },
}

# EXPERIMENTAL -- MAY CHANGE AT ANY TIME: A mapping of package names to a set of proc_macro dependencies for the Rust targets of that package.
_PROC_MACRO_DEPENDENCIES = {
    "third_party/tock/crates": {
    },
}

# EXPERIMENTAL -- MAY CHANGE AT ANY TIME: A mapping of package names to a set of normal dev dependencies for the Rust targets of that package.
_DEV_DEPENDENCIES = {
    "third_party/tock/crates": {
    },
}

# EXPERIMENTAL -- MAY CHANGE AT ANY TIME: A mapping of package names to a set of proc_macro dev dependencies for the Rust targets of that package.
_DEV_PROC_MACRO_DEPENDENCIES = {
    "third_party/tock/crates": {
    },
}

def crate_deps(deps, package_name = None):
    """EXPERIMENTAL -- MAY CHANGE AT ANY TIME: Finds the fully qualified label of the requested crates for the package where this macro is called.

    WARNING: This macro is part of an expeirmental API and is subject to change.

    Args:
        deps (list): The desired list of crate targets.
        package_name (str, optional): The package name of the set of dependencies to look up.
            Defaults to `native.package_name()`.
    Returns:
        list: A list of labels to cargo-raze generated targets (str)
    """

    if not package_name:
        package_name = native.package_name()

    # Join both sets of dependencies
    dependencies = _flatten_dependency_maps([
        _DEPENDENCIES,
        _PROC_MACRO_DEPENDENCIES,
        _DEV_DEPENDENCIES,
        _DEV_PROC_MACRO_DEPENDENCIES,
    ])

    if not deps:
        return []

    missing_crates = []
    crate_targets = []
    for crate_target in deps:
        if crate_target not in dependencies[package_name]:
            missing_crates.append(crate_target)
        else:
            crate_targets.append(dependencies[package_name][crate_target])

    if missing_crates:
        fail("Could not find crates `{}` among dependencies of `{}`. Available dependencies were `{}`".format(
            missing_crates,
            package_name,
            dependencies[package_name],
        ))

    return crate_targets

def all_crate_deps(normal = False, normal_dev = False, proc_macro = False, proc_macro_dev = False, package_name = None):
    """EXPERIMENTAL -- MAY CHANGE AT ANY TIME: Finds the fully qualified label of all requested direct crate dependencies \
    for the package where this macro is called.

    If no parameters are set, all normal dependencies are returned. Setting any one flag will
    otherwise impact the contents of the returned list.

    Args:
        normal (bool, optional): If True, normal dependencies are included in the
            output list. Defaults to False.
        normal_dev (bool, optional): If True, normla dev dependencies will be
            included in the output list. Defaults to False.
        proc_macro (bool, optional): If True, proc_macro dependencies are included
            in the output list. Defaults to False.
        proc_macro_dev (bool, optional): If True, dev proc_macro dependencies are
            included in the output list. Defaults to False.
        package_name (str, optional): The package name of the set of dependencies to look up.
            Defaults to `native.package_name()`.

    Returns:
        list: A list of labels to cargo-raze generated targets (str)
    """

    if not package_name:
        package_name = native.package_name()

    # Determine the relevant maps to use
    all_dependency_maps = []
    if normal:
        all_dependency_maps.append(_DEPENDENCIES)
    if normal_dev:
        all_dependency_maps.append(_DEV_DEPENDENCIES)
    if proc_macro:
        all_dependency_maps.append(_PROC_MACRO_DEPENDENCIES)
    if proc_macro_dev:
        all_dependency_maps.append(_DEV_PROC_MACRO_DEPENDENCIES)

    # Default to always using normal dependencies
    if not all_dependency_maps:
        all_dependency_maps.append(_DEPENDENCIES)

    dependencies = _flatten_dependency_maps(all_dependency_maps)

    if not dependencies:
        return []

    return dependencies[package_name].values()

def _flatten_dependency_maps(all_dependency_maps):
    """Flatten a list of dependency maps into one dictionary.

    Dependency maps have the following structure:

    ```python
    DEPENDENCIES_MAP = {
        # The first key in the map is a Bazel package
        # name of the workspace this file is defined in.
        "package_name": {

            # An alias to a crate target.     # The label of the crate target the
            # Aliases are only crate names.   # alias refers to.
            "alias":                          "@full//:label",
        }
    }
    ```

    Args:
        all_dependency_maps (list): A list of dicts as described above

    Returns:
        dict: A dictionary as described above
    """
    dependencies = {}

    for dep_map in all_dependency_maps:
        for pkg_name in dep_map:
            if pkg_name not in dependencies:
                # Add a non-frozen dict to the collection of dependencies
                dependencies.setdefault(pkg_name, dict(dep_map[pkg_name].items()))
                continue

            duplicate_crate_aliases = [key for key in dependencies[pkg_name] if key in dep_map[pkg_name]]
            if duplicate_crate_aliases:
                fail("There should be no duplicate crate aliases: {}".format(duplicate_crate_aliases))

            dependencies[pkg_name].update(dep_map[pkg_name])

    return dependencies

def raze_fetch_remote_crates(
        # Each of these may be used to temporarily override the location of
        # the crate to a path on your local filesystem for local development
        # of crates you may be using in your project.
        capsules__0_1_0=None,

        components__0_1_0=None,

        earlgrey__0_1_0=None,

        earlgrey_cw310__0_1_0=None,

        enum_primitive__0_1_0=None,

        kernel__0_1_0=None,

        libtock2__0_1_0=None,

        libtock_buttons__0_1_0=None,

        libtock_console__0_1_0=None,

        libtock_debug_panic__0_1_0=None,

        libtock_leds__0_1_0=None,

        libtock_low_level_debug__0_1_0=None,

        libtock_platform__0_1_0=None,

        libtock_runtime__0_1_0=None,

        lowrisc__0_1_0=None,

        riscv__0_1_0=None,

        riscv_csr__0_1_0=None,

        rv32i__0_1_0=None,

        tickv__0_1_0=None,

        tock_cells__0_1_0=None,

        tock_registers__0_7_0=None,

        tock_tbf__0_1_0=None,

    ):
    """This function defines a collection of repos and should be called in a WORKSPACE file"""
    if capsules__0_1_0:
        maybe(
            native.new_local_repository,
            name = "raze__capsules__0_1_0",
            path = capsules__0_1_0,
            build_file = "//third_party/tock/crates/remote:BUILD.capsules-0.1.0.bazel",
        )
    else:
        maybe(
            new_git_repository,
            name = "raze__capsules__0_1_0",
            remote = "https://github.com/cfrantz/tock",
            commit = "b6bc0863a1b155758fdac00d8f660cafc4a786ee",
            build_file = Label("//third_party/tock/crates/remote:BUILD.capsules-0.1.0.bazel"),
            init_submodules = True,
        )

    if components__0_1_0:
        maybe(
            native.new_local_repository,
            name = "raze__components__0_1_0",
            path = components__0_1_0,
            build_file = "//third_party/tock/crates/remote:BUILD.components-0.1.0.bazel",
        )
    else:
        maybe(
            new_git_repository,
            name = "raze__components__0_1_0",
            remote = "https://github.com/cfrantz/tock",
            commit = "b6bc0863a1b155758fdac00d8f660cafc4a786ee",
            build_file = Label("//third_party/tock/crates/remote:BUILD.components-0.1.0.bazel"),
            init_submodules = True,
        )

    if earlgrey__0_1_0:
        maybe(
            native.new_local_repository,
            name = "raze__earlgrey__0_1_0",
            path = earlgrey__0_1_0,
            build_file = "//third_party/tock/crates/remote:BUILD.earlgrey-0.1.0.bazel",
        )
    else:
        maybe(
            new_git_repository,
            name = "raze__earlgrey__0_1_0",
            remote = "https://github.com/cfrantz/tock",
            commit = "b6bc0863a1b155758fdac00d8f660cafc4a786ee",
            build_file = Label("//third_party/tock/crates/remote:BUILD.earlgrey-0.1.0.bazel"),
            init_submodules = True,
        )

    if earlgrey_cw310__0_1_0:
        maybe(
            native.new_local_repository,
            name = "raze__earlgrey_cw310__0_1_0",
            path = earlgrey_cw310__0_1_0,
            build_file = "//third_party/tock/crates/remote:BUILD.earlgrey-cw310-0.1.0.bazel",
        )
    else:
        maybe(
            new_git_repository,
            name = "raze__earlgrey_cw310__0_1_0",
            remote = "https://github.com/cfrantz/tock",
            commit = "b6bc0863a1b155758fdac00d8f660cafc4a786ee",
            build_file = Label("//third_party/tock/crates/remote:BUILD.earlgrey-cw310-0.1.0.bazel"),
            init_submodules = True,
        )

    if enum_primitive__0_1_0:
        maybe(
            native.new_local_repository,
            name = "raze__enum_primitive__0_1_0",
            path = enum_primitive__0_1_0,
            build_file = "//third_party/tock/crates/remote:BUILD.enum_primitive-0.1.0.bazel",
        )
    else:
        maybe(
            new_git_repository,
            name = "raze__enum_primitive__0_1_0",
            remote = "https://github.com/cfrantz/tock",
            commit = "b6bc0863a1b155758fdac00d8f660cafc4a786ee",
            build_file = Label("//third_party/tock/crates/remote:BUILD.enum_primitive-0.1.0.bazel"),
            init_submodules = True,
        )

    if kernel__0_1_0:
        maybe(
            native.new_local_repository,
            name = "raze__kernel__0_1_0",
            path = kernel__0_1_0,
            build_file = "//third_party/tock/crates/remote:BUILD.kernel-0.1.0.bazel",
        )
    else:
        maybe(
            new_git_repository,
            name = "raze__kernel__0_1_0",
            remote = "https://github.com/cfrantz/tock",
            commit = "b6bc0863a1b155758fdac00d8f660cafc4a786ee",
            build_file = Label("//third_party/tock/crates/remote:BUILD.kernel-0.1.0.bazel"),
            init_submodules = True,
        )

    if libtock2__0_1_0:
        maybe(
            native.new_local_repository,
            name = "raze__libtock2__0_1_0",
            path = libtock2__0_1_0,
            build_file = "//third_party/tock/crates/remote:BUILD.libtock2-0.1.0.bazel",
        )
    else:
        maybe(
            new_git_repository,
            name = "raze__libtock2__0_1_0",
            remote = "https://github.com/tock/libtock-rs",
            commit = "1d20b3e19a9c340ea0799bd4fa0397a672fd8f52",
            build_file = Label("//third_party/tock/crates/remote:BUILD.libtock2-0.1.0.bazel"),
            init_submodules = False,
        )

    if libtock_buttons__0_1_0:
        maybe(
            native.new_local_repository,
            name = "raze__libtock_buttons__0_1_0",
            path = libtock_buttons__0_1_0,
            build_file = "//third_party/tock/crates/remote:BUILD.libtock_buttons-0.1.0.bazel",
        )
    else:
        maybe(
            new_git_repository,
            name = "raze__libtock_buttons__0_1_0",
            remote = "https://github.com/tock/libtock-rs",
            commit = "1d20b3e19a9c340ea0799bd4fa0397a672fd8f52",
            build_file = Label("//third_party/tock/crates/remote:BUILD.libtock_buttons-0.1.0.bazel"),
            init_submodules = False,
        )

    if libtock_console__0_1_0:
        maybe(
            native.new_local_repository,
            name = "raze__libtock_console__0_1_0",
            path = libtock_console__0_1_0,
            build_file = "//third_party/tock/crates/remote:BUILD.libtock_console-0.1.0.bazel",
        )
    else:
        maybe(
            new_git_repository,
            name = "raze__libtock_console__0_1_0",
            remote = "https://github.com/tock/libtock-rs",
            commit = "1d20b3e19a9c340ea0799bd4fa0397a672fd8f52",
            build_file = Label("//third_party/tock/crates/remote:BUILD.libtock_console-0.1.0.bazel"),
            init_submodules = False,
        )

    if libtock_debug_panic__0_1_0:
        maybe(
            native.new_local_repository,
            name = "raze__libtock_debug_panic__0_1_0",
            path = libtock_debug_panic__0_1_0,
            build_file = "//third_party/tock/crates/remote:BUILD.libtock_debug_panic-0.1.0.bazel",
        )
    else:
        maybe(
            new_git_repository,
            name = "raze__libtock_debug_panic__0_1_0",
            remote = "https://github.com/tock/libtock-rs",
            commit = "1d20b3e19a9c340ea0799bd4fa0397a672fd8f52",
            build_file = Label("//third_party/tock/crates/remote:BUILD.libtock_debug_panic-0.1.0.bazel"),
            init_submodules = False,
        )

    if libtock_leds__0_1_0:
        maybe(
            native.new_local_repository,
            name = "raze__libtock_leds__0_1_0",
            path = libtock_leds__0_1_0,
            build_file = "//third_party/tock/crates/remote:BUILD.libtock_leds-0.1.0.bazel",
        )
    else:
        maybe(
            new_git_repository,
            name = "raze__libtock_leds__0_1_0",
            remote = "https://github.com/tock/libtock-rs",
            commit = "1d20b3e19a9c340ea0799bd4fa0397a672fd8f52",
            build_file = Label("//third_party/tock/crates/remote:BUILD.libtock_leds-0.1.0.bazel"),
            init_submodules = False,
        )

    if libtock_low_level_debug__0_1_0:
        maybe(
            native.new_local_repository,
            name = "raze__libtock_low_level_debug__0_1_0",
            path = libtock_low_level_debug__0_1_0,
            build_file = "//third_party/tock/crates/remote:BUILD.libtock_low_level_debug-0.1.0.bazel",
        )
    else:
        maybe(
            new_git_repository,
            name = "raze__libtock_low_level_debug__0_1_0",
            remote = "https://github.com/tock/libtock-rs",
            commit = "1d20b3e19a9c340ea0799bd4fa0397a672fd8f52",
            build_file = Label("//third_party/tock/crates/remote:BUILD.libtock_low_level_debug-0.1.0.bazel"),
            init_submodules = False,
        )

    if libtock_platform__0_1_0:
        maybe(
            native.new_local_repository,
            name = "raze__libtock_platform__0_1_0",
            path = libtock_platform__0_1_0,
            build_file = "//third_party/tock/crates/remote:BUILD.libtock_platform-0.1.0.bazel",
        )
    else:
        maybe(
            new_git_repository,
            name = "raze__libtock_platform__0_1_0",
            remote = "https://github.com/tock/libtock-rs",
            commit = "1d20b3e19a9c340ea0799bd4fa0397a672fd8f52",
            build_file = Label("//third_party/tock/crates/remote:BUILD.libtock_platform-0.1.0.bazel"),
            init_submodules = False,
        )

    if libtock_runtime__0_1_0:
        maybe(
            native.new_local_repository,
            name = "raze__libtock_runtime__0_1_0",
            path = libtock_runtime__0_1_0,
            build_file = "//third_party/tock/crates/remote:BUILD.libtock_runtime-0.1.0.bazel",
        )
    else:
        maybe(
            new_git_repository,
            name = "raze__libtock_runtime__0_1_0",
            remote = "https://github.com/tock/libtock-rs",
            commit = "1d20b3e19a9c340ea0799bd4fa0397a672fd8f52",
            build_file = Label("//third_party/tock/crates/remote:BUILD.libtock_runtime-0.1.0.bazel"),
            init_submodules = False,
        )

    if lowrisc__0_1_0:
        maybe(
            native.new_local_repository,
            name = "raze__lowrisc__0_1_0",
            path = lowrisc__0_1_0,
            build_file = "//third_party/tock/crates/remote:BUILD.lowrisc-0.1.0.bazel",
        )
    else:
        maybe(
            new_git_repository,
            name = "raze__lowrisc__0_1_0",
            remote = "https://github.com/cfrantz/tock",
            commit = "b6bc0863a1b155758fdac00d8f660cafc4a786ee",
            build_file = Label("//third_party/tock/crates/remote:BUILD.lowrisc-0.1.0.bazel"),
            init_submodules = True,
        )

    if riscv__0_1_0:
        maybe(
            native.new_local_repository,
            name = "raze__riscv__0_1_0",
            path = riscv__0_1_0,
            build_file = "//third_party/tock/crates/remote:BUILD.riscv-0.1.0.bazel",
        )
    else:
        maybe(
            new_git_repository,
            name = "raze__riscv__0_1_0",
            remote = "https://github.com/cfrantz/tock",
            commit = "b6bc0863a1b155758fdac00d8f660cafc4a786ee",
            build_file = Label("//third_party/tock/crates/remote:BUILD.riscv-0.1.0.bazel"),
            init_submodules = True,
        )

    if riscv_csr__0_1_0:
        maybe(
            native.new_local_repository,
            name = "raze__riscv_csr__0_1_0",
            path = riscv_csr__0_1_0,
            build_file = "//third_party/tock/crates/remote:BUILD.riscv-csr-0.1.0.bazel",
        )
    else:
        maybe(
            new_git_repository,
            name = "raze__riscv_csr__0_1_0",
            remote = "https://github.com/cfrantz/tock",
            commit = "b6bc0863a1b155758fdac00d8f660cafc4a786ee",
            build_file = Label("//third_party/tock/crates/remote:BUILD.riscv-csr-0.1.0.bazel"),
            init_submodules = True,
        )

    if rv32i__0_1_0:
        maybe(
            native.new_local_repository,
            name = "raze__rv32i__0_1_0",
            path = rv32i__0_1_0,
            build_file = "//third_party/tock/crates/remote:BUILD.rv32i-0.1.0.bazel",
        )
    else:
        maybe(
            new_git_repository,
            name = "raze__rv32i__0_1_0",
            remote = "https://github.com/cfrantz/tock",
            commit = "b6bc0863a1b155758fdac00d8f660cafc4a786ee",
            build_file = Label("//third_party/tock/crates/remote:BUILD.rv32i-0.1.0.bazel"),
            init_submodules = True,
        )

    if tickv__0_1_0:
        maybe(
            native.new_local_repository,
            name = "raze__tickv__0_1_0",
            path = tickv__0_1_0,
            build_file = "//third_party/tock/crates/remote:BUILD.tickv-0.1.0.bazel",
        )
    else:
        maybe(
            new_git_repository,
            name = "raze__tickv__0_1_0",
            remote = "https://github.com/cfrantz/tock",
            commit = "b6bc0863a1b155758fdac00d8f660cafc4a786ee",
            build_file = Label("//third_party/tock/crates/remote:BUILD.tickv-0.1.0.bazel"),
            init_submodules = True,
        )

    if tock_cells__0_1_0:
        maybe(
            native.new_local_repository,
            name = "raze__tock_cells__0_1_0",
            path = tock_cells__0_1_0,
            build_file = "//third_party/tock/crates/remote:BUILD.tock-cells-0.1.0.bazel",
        )
    else:
        maybe(
            new_git_repository,
            name = "raze__tock_cells__0_1_0",
            remote = "https://github.com/cfrantz/tock",
            commit = "b6bc0863a1b155758fdac00d8f660cafc4a786ee",
            build_file = Label("//third_party/tock/crates/remote:BUILD.tock-cells-0.1.0.bazel"),
            init_submodules = True,
        )

    if tock_registers__0_7_0:
        maybe(
            native.new_local_repository,
            name = "raze__tock_registers__0_7_0",
            path = tock_registers__0_7_0,
            build_file = "//third_party/tock/crates/remote:BUILD.tock-registers-0.7.0.bazel",
        )
    else:
        maybe(
            new_git_repository,
            name = "raze__tock_registers__0_7_0",
            remote = "https://github.com/cfrantz/tock",
            commit = "b6bc0863a1b155758fdac00d8f660cafc4a786ee",
            build_file = Label("//third_party/tock/crates/remote:BUILD.tock-registers-0.7.0.bazel"),
            init_submodules = True,
        )

    if tock_tbf__0_1_0:
        maybe(
            native.new_local_repository,
            name = "raze__tock_tbf__0_1_0",
            path = tock_tbf__0_1_0,
            build_file = "//third_party/tock/crates/remote:BUILD.tock-tbf-0.1.0.bazel",
        )
    else:
        maybe(
            new_git_repository,
            name = "raze__tock_tbf__0_1_0",
            remote = "https://github.com/cfrantz/tock",
            commit = "b6bc0863a1b155758fdac00d8f660cafc4a786ee",
            build_file = Label("//third_party/tock/crates/remote:BUILD.tock-tbf-0.1.0.bazel"),
            init_submodules = True,
        )

