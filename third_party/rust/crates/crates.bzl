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
    "third_party/rust/crates": {
        "anyhow": "@raze__anyhow__1_0_64//:anyhow",
        "bitflags": "@raze__bitflags__1_3_2//:bitflags",
        "byteorder": "@raze__byteorder__1_4_3//:byteorder",
        "chrono": "@raze__chrono__0_4_22//:chrono",
        "crc": "@raze__crc__3_0_0//:crc",
        "deser-hjson": "@raze__deser_hjson__1_0_2//:deser_hjson",
        "directories": "@raze__directories__4_0_1//:directories",
        "env_logger": "@raze__env_logger__0_8_4//:env_logger",
        "erased-serde": "@raze__erased_serde__0_3_23//:erased_serde",
        "hex": "@raze__hex__0_4_3//:hex",
        "humantime": "@raze__humantime__2_1_0//:humantime",
        "indicatif": "@raze__indicatif__0_16_2//:indicatif",
        "lazy_static": "@raze__lazy_static__1_4_0//:lazy_static",
        "log": "@raze__log__0_4_17//:log",
        "memoffset": "@raze__memoffset__0_6_5//:memoffset",
        "mio": "@raze__mio__0_7_14//:mio",
        "mio-signals": "@raze__mio_signals__0_1_5//:mio_signals",
        "nix": "@raze__nix__0_17_0//:nix",
        "num-bigint-dig": "@raze__num_bigint_dig__0_7_0//:num_bigint_dig",
        "num-traits": "@raze__num_traits__0_2_15//:num_traits",
        "num_enum": "@raze__num_enum__0_5_7//:num_enum",
        "object": "@raze__object__0_25_3//:object",
        "proc-macro-error": "@raze__proc_macro_error__1_0_4//:proc_macro_error",
        "proc-macro2": "@raze__proc_macro2__1_0_43//:proc_macro2",
        "quote": "@raze__quote__1_0_21//:quote",
        "rand": "@raze__rand__0_8_5//:rand",
        "raw_tty": "@raze__raw_tty__0_1_0//:raw_tty",
        "regex": "@raze__regex__1_6_0//:regex",
        "rsa": "@raze__rsa__0_5_0//:rsa",
        "rusb": "@raze__rusb__0_8_1//:rusb",
        "serde": "@raze__serde__1_0_144//:serde",
        "serde_json": "@raze__serde_json__1_0_85//:serde_json",
        "serialport": "@raze__serialport__4_2_0//:serialport",
        "sha2": "@raze__sha2__0_10_5//:sha2",
        "shellwords": "@raze__shellwords__1_1_0//:shellwords",
        "structopt": "@raze__structopt__0_3_26//:structopt",
        "syn": "@raze__syn__1_0_99//:syn",
        "tempfile": "@raze__tempfile__3_3_0//:tempfile",
        "thiserror": "@raze__thiserror__1_0_34//:thiserror",
        "typetag": "@raze__typetag__0_1_8//:typetag",
        "zerocopy": "@raze__zerocopy__0_5_0//:zerocopy",
    },
}

# EXPERIMENTAL -- MAY CHANGE AT ANY TIME: A mapping of package names to a set of proc_macro dependencies for the Rust targets of that package.
_PROC_MACRO_DEPENDENCIES = {
    "third_party/rust/crates": {
    },
}

# EXPERIMENTAL -- MAY CHANGE AT ANY TIME: A mapping of package names to a set of normal dev dependencies for the Rust targets of that package.
_DEV_DEPENDENCIES = {
    "third_party/rust/crates": {
    },
}

# EXPERIMENTAL -- MAY CHANGE AT ANY TIME: A mapping of package names to a set of proc_macro dev dependencies for the Rust targets of that package.
_DEV_PROC_MACRO_DEPENDENCIES = {
    "third_party/rust/crates": {
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
        CoreFoundation_sys__0_1_4=None,

        IOKit_sys__0_1_5=None,

        addr2line__0_17_0=None,

        adler__1_0_2=None,

        aho_corasick__0_7_19=None,

        android_system_properties__0_1_5=None,

        ansi_term__0_12_1=None,

        anyhow__1_0_64=None,

        atty__0_2_14=None,

        autocfg__0_1_8=None,

        autocfg__1_1_0=None,

        backtrace__0_3_66=None,

        base64ct__1_1_1=None,

        bitflags__1_3_2=None,

        block_buffer__0_10_3=None,

        bumpalo__3_11_0=None,

        byteorder__1_4_3=None,

        cc__1_0_73=None,

        cfg_if__0_1_10=None,

        cfg_if__1_0_0=None,

        chrono__0_4_22=None,

        clap__2_34_0=None,

        console__0_15_1=None,

        const_oid__0_6_2=None,

        core_foundation_sys__0_8_3=None,

        cpufeatures__0_2_5=None,

        crc__3_0_0=None,

        crc_catalog__2_1_0=None,

        crc32fast__1_3_2=None,

        crypto_bigint__0_2_11=None,

        crypto_common__0_1_6=None,

        ctor__0_1_23=None,

        der__0_4_5=None,

        derive_more__0_14_1=None,

        deser_hjson__1_0_2=None,

        digest__0_10_3=None,

        digest__0_9_0=None,

        directories__4_0_1=None,

        dirs_sys__0_3_7=None,

        encode_unicode__0_3_6=None,

        env_logger__0_8_4=None,

        erased_serde__0_3_23=None,

        fastrand__1_8_0=None,

        flate2__1_0_24=None,

        generic_array__0_14_6=None,

        getrandom__0_2_7=None,

        ghost__0_1_6=None,

        gimli__0_26_2=None,

        heck__0_3_3=None,

        hermit_abi__0_1_19=None,

        hex__0_4_3=None,

        humantime__2_1_0=None,

        iana_time_zone__0_1_47=None,

        indicatif__0_16_2=None,

        instant__0_1_12=None,

        inventory__0_2_3=None,

        itoa__1_0_3=None,

        js_sys__0_3_60=None,

        lazy_static__1_4_0=None,

        libc__0_2_132=None,

        libm__0_2_5=None,

        libudev__0_3_0=None,

        libudev_sys__0_1_4=None,

        libusb1_sys__0_5_0=None,

        log__0_4_17=None,

        mach__0_1_2=None,

        mach__0_3_2=None,

        memchr__2_5_0=None,

        memoffset__0_6_5=None,

        miniz_oxide__0_5_4=None,

        mio__0_7_14=None,

        mio_signals__0_1_5=None,

        miow__0_3_7=None,

        nix__0_17_0=None,

        nix__0_24_2=None,

        ntapi__0_3_7=None,

        num_bigint_dig__0_7_0=None,

        num_integer__0_1_45=None,

        num_iter__0_1_43=None,

        num_traits__0_2_15=None,

        num_enum__0_5_7=None,

        num_enum_derive__0_5_7=None,

        number_prefix__0_4_0=None,

        object__0_25_3=None,

        object__0_29_0=None,

        once_cell__1_14_0=None,

        pem_rfc7468__0_2_4=None,

        pkcs1__0_2_4=None,

        pkcs8__0_7_6=None,

        pkg_config__0_3_25=None,

        ppv_lite86__0_2_16=None,

        proc_macro_crate__1_2_1=None,

        proc_macro_error__1_0_4=None,

        proc_macro_error_attr__1_0_4=None,

        proc_macro2__0_4_30=None,

        proc_macro2__1_0_43=None,

        quote__0_6_13=None,

        quote__1_0_21=None,

        rand__0_8_5=None,

        rand_chacha__0_3_1=None,

        rand_core__0_6_3=None,

        raw_tty__0_1_0=None,

        redox_syscall__0_2_16=None,

        redox_users__0_4_3=None,

        regex__1_6_0=None,

        regex_syntax__0_6_27=None,

        remove_dir_all__0_5_3=None,

        rsa__0_5_0=None,

        rusb__0_8_1=None,

        rustc_demangle__0_1_21=None,

        rustc_version__0_2_3=None,

        ryu__1_0_11=None,

        semver__0_9_0=None,

        semver_parser__0_7_0=None,

        serde__1_0_144=None,

        serde_derive__1_0_144=None,

        serde_json__1_0_85=None,

        serialport__4_2_0=None,

        sha2__0_10_5=None,

        shellwords__1_1_0=None,

        smallvec__1_9_0=None,

        spin__0_5_2=None,

        spki__0_4_1=None,

        strsim__0_8_0=None,

        structopt__0_3_26=None,

        structopt_derive__0_4_18=None,

        subtle__2_4_1=None,

        syn__0_15_44=None,

        syn__1_0_99=None,

        synstructure__0_12_6=None,

        tempfile__3_3_0=None,

        termcolor__1_1_3=None,

        terminal_size__0_1_17=None,

        textwrap__0_11_0=None,

        thiserror__1_0_34=None,

        thiserror_impl__1_0_34=None,

        time__0_1_44=None,

        toml__0_5_9=None,

        typenum__1_15_0=None,

        typetag__0_1_8=None,

        typetag_impl__0_1_8=None,

        unicode_ident__1_0_3=None,

        unicode_segmentation__1_9_0=None,

        unicode_width__0_1_9=None,

        unicode_xid__0_1_0=None,

        unicode_xid__0_2_3=None,

        vcpkg__0_2_15=None,

        vec_map__0_8_2=None,

        version_check__0_9_4=None,

        void__1_0_2=None,

        wasi__0_10_0_wasi_snapshot_preview1=None,

        wasi__0_11_0_wasi_snapshot_preview1=None,

        wasm_bindgen__0_2_83=None,

        wasm_bindgen_backend__0_2_83=None,

        wasm_bindgen_macro__0_2_83=None,

        wasm_bindgen_macro_support__0_2_83=None,

        wasm_bindgen_shared__0_2_83=None,

        winapi__0_3_9=None,

        winapi_i686_pc_windows_gnu__0_4_0=None,

        winapi_util__0_1_5=None,

        winapi_x86_64_pc_windows_gnu__0_4_0=None,

        zerocopy__0_5_0=None,

        zerocopy_derive__0_3_1=None,

        zeroize__1_4_3=None,

        zeroize_derive__1_3_2=None,

    ):
    """This function defines a collection of repos and should be called in a WORKSPACE file"""
    if CoreFoundation_sys__0_1_4:
        maybe(
            native.new_local_repository,
            name = "raze__CoreFoundation_sys__0_1_4",
            path = CoreFoundation_sys__0_1_4,
            build_file = "//third_party/rust/crates/remote:BUILD.CoreFoundation-sys-0.1.4.bazel",
        )
    else:
        maybe(
            http_archive,
            name = "raze__CoreFoundation_sys__0_1_4",
            url = "https://crates.io/api/v1/crates/CoreFoundation-sys/0.1.4/download",
            type = "tar.gz",
            sha256 = "d0e9889e6db118d49d88d84728d0e964d973a5680befb5f85f55141beea5c20b",
            strip_prefix = "CoreFoundation-sys-0.1.4",
            build_file = Label("//third_party/rust/crates/remote:BUILD.CoreFoundation-sys-0.1.4.bazel"),
        )

    if IOKit_sys__0_1_5:
        maybe(
            native.new_local_repository,
            name = "raze__IOKit_sys__0_1_5",
            path = IOKit_sys__0_1_5,
            build_file = "//third_party/rust/crates/remote:BUILD.IOKit-sys-0.1.5.bazel",
        )
    else:
        maybe(
            http_archive,
            name = "raze__IOKit_sys__0_1_5",
            url = "https://crates.io/api/v1/crates/IOKit-sys/0.1.5/download",
            type = "tar.gz",
            sha256 = "99696c398cbaf669d2368076bdb3d627fb0ce51a26899d7c61228c5c0af3bf4a",
            strip_prefix = "IOKit-sys-0.1.5",
            build_file = Label("//third_party/rust/crates/remote:BUILD.IOKit-sys-0.1.5.bazel"),
        )

    if addr2line__0_17_0:
        maybe(
            native.new_local_repository,
            name = "raze__addr2line__0_17_0",
            path = addr2line__0_17_0,
            build_file = "//third_party/rust/crates/remote:BUILD.addr2line-0.17.0.bazel",
        )
    else:
        maybe(
            http_archive,
            name = "raze__addr2line__0_17_0",
            url = "https://crates.io/api/v1/crates/addr2line/0.17.0/download",
            type = "tar.gz",
            sha256 = "b9ecd88a8c8378ca913a680cd98f0f13ac67383d35993f86c90a70e3f137816b",
            strip_prefix = "addr2line-0.17.0",
            build_file = Label("//third_party/rust/crates/remote:BUILD.addr2line-0.17.0.bazel"),
        )

    if adler__1_0_2:
        maybe(
            native.new_local_repository,
            name = "raze__adler__1_0_2",
            path = adler__1_0_2,
            build_file = "//third_party/rust/crates/remote:BUILD.adler-1.0.2.bazel",
        )
    else:
        maybe(
            http_archive,
            name = "raze__adler__1_0_2",
            url = "https://crates.io/api/v1/crates/adler/1.0.2/download",
            type = "tar.gz",
            sha256 = "f26201604c87b1e01bd3d98f8d5d9a8fcbb815e8cedb41ffccbeb4bf593a35fe",
            strip_prefix = "adler-1.0.2",
            build_file = Label("//third_party/rust/crates/remote:BUILD.adler-1.0.2.bazel"),
        )

    if aho_corasick__0_7_19:
        maybe(
            native.new_local_repository,
            name = "raze__aho_corasick__0_7_19",
            path = aho_corasick__0_7_19,
            build_file = "//third_party/rust/crates/remote:BUILD.aho-corasick-0.7.19.bazel",
        )
    else:
        maybe(
            http_archive,
            name = "raze__aho_corasick__0_7_19",
            url = "https://crates.io/api/v1/crates/aho-corasick/0.7.19/download",
            type = "tar.gz",
            sha256 = "b4f55bd91a0978cbfd91c457a164bab8b4001c833b7f323132c0a4e1922dd44e",
            strip_prefix = "aho-corasick-0.7.19",
            build_file = Label("//third_party/rust/crates/remote:BUILD.aho-corasick-0.7.19.bazel"),
        )

    if android_system_properties__0_1_5:
        maybe(
            native.new_local_repository,
            name = "raze__android_system_properties__0_1_5",
            path = android_system_properties__0_1_5,
            build_file = "//third_party/rust/crates/remote:BUILD.android_system_properties-0.1.5.bazel",
        )
    else:
        maybe(
            http_archive,
            name = "raze__android_system_properties__0_1_5",
            url = "https://crates.io/api/v1/crates/android_system_properties/0.1.5/download",
            type = "tar.gz",
            sha256 = "819e7219dbd41043ac279b19830f2efc897156490d7fd6ea916720117ee66311",
            strip_prefix = "android_system_properties-0.1.5",
            build_file = Label("//third_party/rust/crates/remote:BUILD.android_system_properties-0.1.5.bazel"),
        )

    if ansi_term__0_12_1:
        maybe(
            native.new_local_repository,
            name = "raze__ansi_term__0_12_1",
            path = ansi_term__0_12_1,
            build_file = "//third_party/rust/crates/remote:BUILD.ansi_term-0.12.1.bazel",
        )
    else:
        maybe(
            http_archive,
            name = "raze__ansi_term__0_12_1",
            url = "https://crates.io/api/v1/crates/ansi_term/0.12.1/download",
            type = "tar.gz",
            sha256 = "d52a9bb7ec0cf484c551830a7ce27bd20d67eac647e1befb56b0be4ee39a55d2",
            strip_prefix = "ansi_term-0.12.1",
            build_file = Label("//third_party/rust/crates/remote:BUILD.ansi_term-0.12.1.bazel"),
        )

    if anyhow__1_0_64:
        maybe(
            native.new_local_repository,
            name = "raze__anyhow__1_0_64",
            path = anyhow__1_0_64,
            build_file = "//third_party/rust/crates/remote:BUILD.anyhow-1.0.64.bazel",
        )
    else:
        maybe(
            http_archive,
            name = "raze__anyhow__1_0_64",
            url = "https://crates.io/api/v1/crates/anyhow/1.0.64/download",
            type = "tar.gz",
            sha256 = "b9a8f622bcf6ff3df478e9deba3e03e4e04b300f8e6a139e192c05fa3490afc7",
            strip_prefix = "anyhow-1.0.64",
            build_file = Label("//third_party/rust/crates/remote:BUILD.anyhow-1.0.64.bazel"),
        )

    if atty__0_2_14:
        maybe(
            native.new_local_repository,
            name = "raze__atty__0_2_14",
            path = atty__0_2_14,
            build_file = "//third_party/rust/crates/remote:BUILD.atty-0.2.14.bazel",
        )
    else:
        maybe(
            http_archive,
            name = "raze__atty__0_2_14",
            url = "https://crates.io/api/v1/crates/atty/0.2.14/download",
            type = "tar.gz",
            sha256 = "d9b39be18770d11421cdb1b9947a45dd3f37e93092cbf377614828a319d5fee8",
            strip_prefix = "atty-0.2.14",
            build_file = Label("//third_party/rust/crates/remote:BUILD.atty-0.2.14.bazel"),
        )

    if autocfg__0_1_8:
        maybe(
            native.new_local_repository,
            name = "raze__autocfg__0_1_8",
            path = autocfg__0_1_8,
            build_file = "//third_party/rust/crates/remote:BUILD.autocfg-0.1.8.bazel",
        )
    else:
        maybe(
            http_archive,
            name = "raze__autocfg__0_1_8",
            url = "https://crates.io/api/v1/crates/autocfg/0.1.8/download",
            type = "tar.gz",
            sha256 = "0dde43e75fd43e8a1bf86103336bc699aa8d17ad1be60c76c0bdfd4828e19b78",
            strip_prefix = "autocfg-0.1.8",
            build_file = Label("//third_party/rust/crates/remote:BUILD.autocfg-0.1.8.bazel"),
        )

    if autocfg__1_1_0:
        maybe(
            native.new_local_repository,
            name = "raze__autocfg__1_1_0",
            path = autocfg__1_1_0,
            build_file = "//third_party/rust/crates/remote:BUILD.autocfg-1.1.0.bazel",
        )
    else:
        maybe(
            http_archive,
            name = "raze__autocfg__1_1_0",
            url = "https://crates.io/api/v1/crates/autocfg/1.1.0/download",
            type = "tar.gz",
            sha256 = "d468802bab17cbc0cc575e9b053f41e72aa36bfa6b7f55e3529ffa43161b97fa",
            strip_prefix = "autocfg-1.1.0",
            build_file = Label("//third_party/rust/crates/remote:BUILD.autocfg-1.1.0.bazel"),
        )

    if backtrace__0_3_66:
        maybe(
            native.new_local_repository,
            name = "raze__backtrace__0_3_66",
            path = backtrace__0_3_66,
            build_file = "//third_party/rust/crates/remote:BUILD.backtrace-0.3.66.bazel",
        )
    else:
        maybe(
            http_archive,
            name = "raze__backtrace__0_3_66",
            url = "https://crates.io/api/v1/crates/backtrace/0.3.66/download",
            type = "tar.gz",
            sha256 = "cab84319d616cfb654d03394f38ab7e6f0919e181b1b57e1fd15e7fb4077d9a7",
            strip_prefix = "backtrace-0.3.66",
            build_file = Label("//third_party/rust/crates/remote:BUILD.backtrace-0.3.66.bazel"),
        )

    if base64ct__1_1_1:
        maybe(
            native.new_local_repository,
            name = "raze__base64ct__1_1_1",
            path = base64ct__1_1_1,
            build_file = "//third_party/rust/crates/remote:BUILD.base64ct-1.1.1.bazel",
        )
    else:
        maybe(
            http_archive,
            name = "raze__base64ct__1_1_1",
            url = "https://crates.io/api/v1/crates/base64ct/1.1.1/download",
            type = "tar.gz",
            sha256 = "e6b4d9b1225d28d360ec6a231d65af1fd99a2a095154c8040689617290569c5c",
            strip_prefix = "base64ct-1.1.1",
            build_file = Label("//third_party/rust/crates/remote:BUILD.base64ct-1.1.1.bazel"),
        )

    if bitflags__1_3_2:
        maybe(
            native.new_local_repository,
            name = "raze__bitflags__1_3_2",
            path = bitflags__1_3_2,
            build_file = "//third_party/rust/crates/remote:BUILD.bitflags-1.3.2.bazel",
        )
    else:
        maybe(
            http_archive,
            name = "raze__bitflags__1_3_2",
            url = "https://crates.io/api/v1/crates/bitflags/1.3.2/download",
            type = "tar.gz",
            sha256 = "bef38d45163c2f1dde094a7dfd33ccf595c92905c8f8f4fdc18d06fb1037718a",
            strip_prefix = "bitflags-1.3.2",
            build_file = Label("//third_party/rust/crates/remote:BUILD.bitflags-1.3.2.bazel"),
        )

    if block_buffer__0_10_3:
        maybe(
            native.new_local_repository,
            name = "raze__block_buffer__0_10_3",
            path = block_buffer__0_10_3,
            build_file = "//third_party/rust/crates/remote:BUILD.block-buffer-0.10.3.bazel",
        )
    else:
        maybe(
            http_archive,
            name = "raze__block_buffer__0_10_3",
            url = "https://crates.io/api/v1/crates/block-buffer/0.10.3/download",
            type = "tar.gz",
            sha256 = "69cce20737498f97b993470a6e536b8523f0af7892a4f928cceb1ac5e52ebe7e",
            strip_prefix = "block-buffer-0.10.3",
            build_file = Label("//third_party/rust/crates/remote:BUILD.block-buffer-0.10.3.bazel"),
        )

    if bumpalo__3_11_0:
        maybe(
            native.new_local_repository,
            name = "raze__bumpalo__3_11_0",
            path = bumpalo__3_11_0,
            build_file = "//third_party/rust/crates/remote:BUILD.bumpalo-3.11.0.bazel",
        )
    else:
        maybe(
            http_archive,
            name = "raze__bumpalo__3_11_0",
            url = "https://crates.io/api/v1/crates/bumpalo/3.11.0/download",
            type = "tar.gz",
            sha256 = "c1ad822118d20d2c234f427000d5acc36eabe1e29a348c89b63dd60b13f28e5d",
            strip_prefix = "bumpalo-3.11.0",
            build_file = Label("//third_party/rust/crates/remote:BUILD.bumpalo-3.11.0.bazel"),
        )

    if byteorder__1_4_3:
        maybe(
            native.new_local_repository,
            name = "raze__byteorder__1_4_3",
            path = byteorder__1_4_3,
            build_file = "//third_party/rust/crates/remote:BUILD.byteorder-1.4.3.bazel",
        )
    else:
        maybe(
            http_archive,
            name = "raze__byteorder__1_4_3",
            url = "https://crates.io/api/v1/crates/byteorder/1.4.3/download",
            type = "tar.gz",
            sha256 = "14c189c53d098945499cdfa7ecc63567cf3886b3332b312a5b4585d8d3a6a610",
            strip_prefix = "byteorder-1.4.3",
            build_file = Label("//third_party/rust/crates/remote:BUILD.byteorder-1.4.3.bazel"),
        )

    if cc__1_0_73:
        maybe(
            native.new_local_repository,
            name = "raze__cc__1_0_73",
            path = cc__1_0_73,
            build_file = "//third_party/rust/crates/remote:BUILD.cc-1.0.73.bazel",
        )
    else:
        maybe(
            http_archive,
            name = "raze__cc__1_0_73",
            url = "https://crates.io/api/v1/crates/cc/1.0.73/download",
            type = "tar.gz",
            sha256 = "2fff2a6927b3bb87f9595d67196a70493f627687a71d87a0d692242c33f58c11",
            strip_prefix = "cc-1.0.73",
            build_file = Label("//third_party/rust/crates/remote:BUILD.cc-1.0.73.bazel"),
        )

    if cfg_if__0_1_10:
        maybe(
            native.new_local_repository,
            name = "raze__cfg_if__0_1_10",
            path = cfg_if__0_1_10,
            build_file = "//third_party/rust/crates/remote:BUILD.cfg-if-0.1.10.bazel",
        )
    else:
        maybe(
            http_archive,
            name = "raze__cfg_if__0_1_10",
            url = "https://crates.io/api/v1/crates/cfg-if/0.1.10/download",
            type = "tar.gz",
            sha256 = "4785bdd1c96b2a846b2bd7cc02e86b6b3dbf14e7e53446c4f54c92a361040822",
            strip_prefix = "cfg-if-0.1.10",
            build_file = Label("//third_party/rust/crates/remote:BUILD.cfg-if-0.1.10.bazel"),
        )

    if cfg_if__1_0_0:
        maybe(
            native.new_local_repository,
            name = "raze__cfg_if__1_0_0",
            path = cfg_if__1_0_0,
            build_file = "//third_party/rust/crates/remote:BUILD.cfg-if-1.0.0.bazel",
        )
    else:
        maybe(
            http_archive,
            name = "raze__cfg_if__1_0_0",
            url = "https://crates.io/api/v1/crates/cfg-if/1.0.0/download",
            type = "tar.gz",
            sha256 = "baf1de4339761588bc0619e3cbc0120ee582ebb74b53b4efbf79117bd2da40fd",
            strip_prefix = "cfg-if-1.0.0",
            build_file = Label("//third_party/rust/crates/remote:BUILD.cfg-if-1.0.0.bazel"),
        )

    if chrono__0_4_22:
        maybe(
            native.new_local_repository,
            name = "raze__chrono__0_4_22",
            path = chrono__0_4_22,
            build_file = "//third_party/rust/crates/remote:BUILD.chrono-0.4.22.bazel",
        )
    else:
        maybe(
            http_archive,
            name = "raze__chrono__0_4_22",
            url = "https://crates.io/api/v1/crates/chrono/0.4.22/download",
            type = "tar.gz",
            sha256 = "bfd4d1b31faaa3a89d7934dbded3111da0d2ef28e3ebccdb4f0179f5929d1ef1",
            strip_prefix = "chrono-0.4.22",
            build_file = Label("//third_party/rust/crates/remote:BUILD.chrono-0.4.22.bazel"),
        )

    if clap__2_34_0:
        maybe(
            native.new_local_repository,
            name = "raze__clap__2_34_0",
            path = clap__2_34_0,
            build_file = "//third_party/rust/crates/remote:BUILD.clap-2.34.0.bazel",
        )
    else:
        maybe(
            http_archive,
            name = "raze__clap__2_34_0",
            url = "https://crates.io/api/v1/crates/clap/2.34.0/download",
            type = "tar.gz",
            sha256 = "a0610544180c38b88101fecf2dd634b174a62eef6946f84dfc6a7127512b381c",
            strip_prefix = "clap-2.34.0",
            build_file = Label("//third_party/rust/crates/remote:BUILD.clap-2.34.0.bazel"),
        )

    if console__0_15_1:
        maybe(
            native.new_local_repository,
            name = "raze__console__0_15_1",
            path = console__0_15_1,
            build_file = "//third_party/rust/crates/remote:BUILD.console-0.15.1.bazel",
        )
    else:
        maybe(
            http_archive,
            name = "raze__console__0_15_1",
            url = "https://crates.io/api/v1/crates/console/0.15.1/download",
            type = "tar.gz",
            sha256 = "89eab4d20ce20cea182308bca13088fecea9c05f6776cf287205d41a0ed3c847",
            strip_prefix = "console-0.15.1",
            build_file = Label("//third_party/rust/crates/remote:BUILD.console-0.15.1.bazel"),
        )

    if const_oid__0_6_2:
        maybe(
            native.new_local_repository,
            name = "raze__const_oid__0_6_2",
            path = const_oid__0_6_2,
            build_file = "//third_party/rust/crates/remote:BUILD.const-oid-0.6.2.bazel",
        )
    else:
        maybe(
            http_archive,
            name = "raze__const_oid__0_6_2",
            url = "https://crates.io/api/v1/crates/const-oid/0.6.2/download",
            type = "tar.gz",
            sha256 = "9d6f2aa4d0537bcc1c74df8755072bd31c1ef1a3a1b85a68e8404a8c353b7b8b",
            strip_prefix = "const-oid-0.6.2",
            build_file = Label("//third_party/rust/crates/remote:BUILD.const-oid-0.6.2.bazel"),
        )

    if core_foundation_sys__0_8_3:
        maybe(
            native.new_local_repository,
            name = "raze__core_foundation_sys__0_8_3",
            path = core_foundation_sys__0_8_3,
            build_file = "//third_party/rust/crates/remote:BUILD.core-foundation-sys-0.8.3.bazel",
        )
    else:
        maybe(
            http_archive,
            name = "raze__core_foundation_sys__0_8_3",
            url = "https://crates.io/api/v1/crates/core-foundation-sys/0.8.3/download",
            type = "tar.gz",
            sha256 = "5827cebf4670468b8772dd191856768aedcb1b0278a04f989f7766351917b9dc",
            strip_prefix = "core-foundation-sys-0.8.3",
            build_file = Label("//third_party/rust/crates/remote:BUILD.core-foundation-sys-0.8.3.bazel"),
        )

    if cpufeatures__0_2_5:
        maybe(
            native.new_local_repository,
            name = "raze__cpufeatures__0_2_5",
            path = cpufeatures__0_2_5,
            build_file = "//third_party/rust/crates/remote:BUILD.cpufeatures-0.2.5.bazel",
        )
    else:
        maybe(
            http_archive,
            name = "raze__cpufeatures__0_2_5",
            url = "https://crates.io/api/v1/crates/cpufeatures/0.2.5/download",
            type = "tar.gz",
            sha256 = "28d997bd5e24a5928dd43e46dc529867e207907fe0b239c3477d924f7f2ca320",
            strip_prefix = "cpufeatures-0.2.5",
            build_file = Label("//third_party/rust/crates/remote:BUILD.cpufeatures-0.2.5.bazel"),
        )

    if crc__3_0_0:
        maybe(
            native.new_local_repository,
            name = "raze__crc__3_0_0",
            path = crc__3_0_0,
            build_file = "//third_party/rust/crates/remote:BUILD.crc-3.0.0.bazel",
        )
    else:
        maybe(
            http_archive,
            name = "raze__crc__3_0_0",
            url = "https://crates.io/api/v1/crates/crc/3.0.0/download",
            type = "tar.gz",
            strip_prefix = "crc-3.0.0",
            build_file = Label("//third_party/rust/crates/remote:BUILD.crc-3.0.0.bazel"),
        )

    if crc_catalog__2_1_0:
        maybe(
            native.new_local_repository,
            name = "raze__crc_catalog__2_1_0",
            path = crc_catalog__2_1_0,
            build_file = "//third_party/rust/crates/remote:BUILD.crc-catalog-2.1.0.bazel",
        )
    else:
        maybe(
            http_archive,
            name = "raze__crc_catalog__2_1_0",
            url = "https://crates.io/api/v1/crates/crc-catalog/2.1.0/download",
            type = "tar.gz",
            strip_prefix = "crc-catalog-2.1.0",
            build_file = Label("//third_party/rust/crates/remote:BUILD.crc-catalog-2.1.0.bazel"),
        )

    if crc32fast__1_3_2:
        maybe(
            native.new_local_repository,
            name = "raze__crc32fast__1_3_2",
            path = crc32fast__1_3_2,
            build_file = "//third_party/rust/crates/remote:BUILD.crc32fast-1.3.2.bazel",
        )
    else:
        maybe(
            http_archive,
            name = "raze__crc32fast__1_3_2",
            url = "https://crates.io/api/v1/crates/crc32fast/1.3.2/download",
            type = "tar.gz",
            sha256 = "b540bd8bc810d3885c6ea91e2018302f68baba2129ab3e88f32389ee9370880d",
            strip_prefix = "crc32fast-1.3.2",
            build_file = Label("//third_party/rust/crates/remote:BUILD.crc32fast-1.3.2.bazel"),
        )

    if crypto_bigint__0_2_11:
        maybe(
            native.new_local_repository,
            name = "raze__crypto_bigint__0_2_11",
            path = crypto_bigint__0_2_11,
            build_file = "//third_party/rust/crates/remote:BUILD.crypto-bigint-0.2.11.bazel",
        )
    else:
        maybe(
            http_archive,
            name = "raze__crypto_bigint__0_2_11",
            url = "https://crates.io/api/v1/crates/crypto-bigint/0.2.11/download",
            type = "tar.gz",
            sha256 = "f83bd3bb4314701c568e340cd8cf78c975aa0ca79e03d3f6d1677d5b0c9c0c03",
            strip_prefix = "crypto-bigint-0.2.11",
            build_file = Label("//third_party/rust/crates/remote:BUILD.crypto-bigint-0.2.11.bazel"),
        )

    if crypto_common__0_1_6:
        maybe(
            native.new_local_repository,
            name = "raze__crypto_common__0_1_6",
            path = crypto_common__0_1_6,
            build_file = "//third_party/rust/crates/remote:BUILD.crypto-common-0.1.6.bazel",
        )
    else:
        maybe(
            http_archive,
            name = "raze__crypto_common__0_1_6",
            url = "https://crates.io/api/v1/crates/crypto-common/0.1.6/download",
            type = "tar.gz",
            sha256 = "1bfb12502f3fc46cca1bb51ac28df9d618d813cdc3d2f25b9fe775a34af26bb3",
            strip_prefix = "crypto-common-0.1.6",
            build_file = Label("//third_party/rust/crates/remote:BUILD.crypto-common-0.1.6.bazel"),
        )

    if ctor__0_1_23:
        maybe(
            native.new_local_repository,
            name = "raze__ctor__0_1_23",
            path = ctor__0_1_23,
            build_file = "//third_party/rust/crates/remote:BUILD.ctor-0.1.23.bazel",
        )
    else:
        maybe(
            http_archive,
            name = "raze__ctor__0_1_23",
            url = "https://crates.io/api/v1/crates/ctor/0.1.23/download",
            type = "tar.gz",
            sha256 = "cdffe87e1d521a10f9696f833fe502293ea446d7f256c06128293a4119bdf4cb",
            strip_prefix = "ctor-0.1.23",
            build_file = Label("//third_party/rust/crates/remote:BUILD.ctor-0.1.23.bazel"),
        )

    if der__0_4_5:
        maybe(
            native.new_local_repository,
            name = "raze__der__0_4_5",
            path = der__0_4_5,
            build_file = "//third_party/rust/crates/remote:BUILD.der-0.4.5.bazel",
        )
    else:
        maybe(
            http_archive,
            name = "raze__der__0_4_5",
            url = "https://crates.io/api/v1/crates/der/0.4.5/download",
            type = "tar.gz",
            sha256 = "79b71cca7d95d7681a4b3b9cdf63c8dbc3730d0584c2c74e31416d64a90493f4",
            strip_prefix = "der-0.4.5",
            build_file = Label("//third_party/rust/crates/remote:BUILD.der-0.4.5.bazel"),
        )

    if derive_more__0_14_1:
        maybe(
            native.new_local_repository,
            name = "raze__derive_more__0_14_1",
            path = derive_more__0_14_1,
            build_file = "//third_party/rust/crates/remote:BUILD.derive_more-0.14.1.bazel",
        )
    else:
        maybe(
            http_archive,
            name = "raze__derive_more__0_14_1",
            url = "https://crates.io/api/v1/crates/derive_more/0.14.1/download",
            type = "tar.gz",
            sha256 = "6d944ac6003ed268757ef1ee686753b57efc5fcf0ebe7b64c9fc81e7e32ff839",
            strip_prefix = "derive_more-0.14.1",
            build_file = Label("//third_party/rust/crates/remote:BUILD.derive_more-0.14.1.bazel"),
        )

    if deser_hjson__1_0_2:
        maybe(
            native.new_local_repository,
            name = "raze__deser_hjson__1_0_2",
            path = deser_hjson__1_0_2,
            build_file = "//third_party/rust/crates/remote:BUILD.deser-hjson-1.0.2.bazel",
        )
    else:
        maybe(
            http_archive,
            name = "raze__deser_hjson__1_0_2",
            url = "https://crates.io/api/v1/crates/deser-hjson/1.0.2/download",
            type = "tar.gz",
            sha256 = "1f486ff51f3ecdf9364736375a4b358b6eb9f02555d5324fa4837c00b5aa23f5",
            strip_prefix = "deser-hjson-1.0.2",
            build_file = Label("//third_party/rust/crates/remote:BUILD.deser-hjson-1.0.2.bazel"),
        )

    if digest__0_10_3:
        maybe(
            native.new_local_repository,
            name = "raze__digest__0_10_3",
            path = digest__0_10_3,
            build_file = "//third_party/rust/crates/remote:BUILD.digest-0.10.3.bazel",
        )
    else:
        maybe(
            http_archive,
            name = "raze__digest__0_10_3",
            url = "https://crates.io/api/v1/crates/digest/0.10.3/download",
            type = "tar.gz",
            sha256 = "f2fb860ca6fafa5552fb6d0e816a69c8e49f0908bf524e30a90d97c85892d506",
            strip_prefix = "digest-0.10.3",
            build_file = Label("//third_party/rust/crates/remote:BUILD.digest-0.10.3.bazel"),
        )

    if digest__0_9_0:
        maybe(
            native.new_local_repository,
            name = "raze__digest__0_9_0",
            path = digest__0_9_0,
            build_file = "//third_party/rust/crates/remote:BUILD.digest-0.9.0.bazel",
        )
    else:
        maybe(
            http_archive,
            name = "raze__digest__0_9_0",
            url = "https://crates.io/api/v1/crates/digest/0.9.0/download",
            type = "tar.gz",
            sha256 = "d3dd60d1080a57a05ab032377049e0591415d2b31afd7028356dbf3cc6dcb066",
            strip_prefix = "digest-0.9.0",
            build_file = Label("//third_party/rust/crates/remote:BUILD.digest-0.9.0.bazel"),
        )

    if directories__4_0_1:
        maybe(
            native.new_local_repository,
            name = "raze__directories__4_0_1",
            path = directories__4_0_1,
            build_file = "//third_party/rust/crates/remote:BUILD.directories-4.0.1.bazel",
        )
    else:
        maybe(
            http_archive,
            name = "raze__directories__4_0_1",
            url = "https://crates.io/api/v1/crates/directories/4.0.1/download",
            type = "tar.gz",
            sha256 = "f51c5d4ddabd36886dd3e1438cb358cdcb0d7c499cb99cb4ac2e38e18b5cb210",
            strip_prefix = "directories-4.0.1",
            build_file = Label("//third_party/rust/crates/remote:BUILD.directories-4.0.1.bazel"),
        )

    if dirs_sys__0_3_7:
        maybe(
            native.new_local_repository,
            name = "raze__dirs_sys__0_3_7",
            path = dirs_sys__0_3_7,
            build_file = "//third_party/rust/crates/remote:BUILD.dirs-sys-0.3.7.bazel",
        )
    else:
        maybe(
            http_archive,
            name = "raze__dirs_sys__0_3_7",
            url = "https://crates.io/api/v1/crates/dirs-sys/0.3.7/download",
            type = "tar.gz",
            sha256 = "1b1d1d91c932ef41c0f2663aa8b0ca0342d444d842c06914aa0a7e352d0bada6",
            strip_prefix = "dirs-sys-0.3.7",
            build_file = Label("//third_party/rust/crates/remote:BUILD.dirs-sys-0.3.7.bazel"),
        )

    if encode_unicode__0_3_6:
        maybe(
            native.new_local_repository,
            name = "raze__encode_unicode__0_3_6",
            path = encode_unicode__0_3_6,
            build_file = "//third_party/rust/crates/remote:BUILD.encode_unicode-0.3.6.bazel",
        )
    else:
        maybe(
            http_archive,
            name = "raze__encode_unicode__0_3_6",
            url = "https://crates.io/api/v1/crates/encode_unicode/0.3.6/download",
            type = "tar.gz",
            sha256 = "a357d28ed41a50f9c765dbfe56cbc04a64e53e5fc58ba79fbc34c10ef3df831f",
            strip_prefix = "encode_unicode-0.3.6",
            build_file = Label("//third_party/rust/crates/remote:BUILD.encode_unicode-0.3.6.bazel"),
        )

    if env_logger__0_8_4:
        maybe(
            native.new_local_repository,
            name = "raze__env_logger__0_8_4",
            path = env_logger__0_8_4,
            build_file = "//third_party/rust/crates/remote:BUILD.env_logger-0.8.4.bazel",
        )
    else:
        maybe(
            http_archive,
            name = "raze__env_logger__0_8_4",
            url = "https://crates.io/api/v1/crates/env_logger/0.8.4/download",
            type = "tar.gz",
            sha256 = "a19187fea3ac7e84da7dacf48de0c45d63c6a76f9490dae389aead16c243fce3",
            strip_prefix = "env_logger-0.8.4",
            build_file = Label("//third_party/rust/crates/remote:BUILD.env_logger-0.8.4.bazel"),
        )

    if erased_serde__0_3_23:
        maybe(
            native.new_local_repository,
            name = "raze__erased_serde__0_3_23",
            path = erased_serde__0_3_23,
            build_file = "//third_party/rust/crates/remote:BUILD.erased-serde-0.3.23.bazel",
        )
    else:
        maybe(
            http_archive,
            name = "raze__erased_serde__0_3_23",
            url = "https://crates.io/api/v1/crates/erased-serde/0.3.23/download",
            type = "tar.gz",
            sha256 = "54558e0ba96fbe24280072642eceb9d7d442e32c7ec0ea9e7ecd7b4ea2cf4e11",
            strip_prefix = "erased-serde-0.3.23",
            build_file = Label("//third_party/rust/crates/remote:BUILD.erased-serde-0.3.23.bazel"),
        )

    if fastrand__1_8_0:
        maybe(
            native.new_local_repository,
            name = "raze__fastrand__1_8_0",
            path = fastrand__1_8_0,
            build_file = "//third_party/rust/crates/remote:BUILD.fastrand-1.8.0.bazel",
        )
    else:
        maybe(
            http_archive,
            name = "raze__fastrand__1_8_0",
            url = "https://crates.io/api/v1/crates/fastrand/1.8.0/download",
            type = "tar.gz",
            sha256 = "a7a407cfaa3385c4ae6b23e84623d48c2798d06e3e6a1878f7f59f17b3f86499",
            strip_prefix = "fastrand-1.8.0",
            build_file = Label("//third_party/rust/crates/remote:BUILD.fastrand-1.8.0.bazel"),
        )

    if flate2__1_0_24:
        maybe(
            native.new_local_repository,
            name = "raze__flate2__1_0_24",
            path = flate2__1_0_24,
            build_file = "//third_party/rust/crates/remote:BUILD.flate2-1.0.24.bazel",
        )
    else:
        maybe(
            http_archive,
            name = "raze__flate2__1_0_24",
            url = "https://crates.io/api/v1/crates/flate2/1.0.24/download",
            type = "tar.gz",
            sha256 = "f82b0f4c27ad9f8bfd1f3208d882da2b09c301bc1c828fd3a00d0216d2fbbff6",
            strip_prefix = "flate2-1.0.24",
            build_file = Label("//third_party/rust/crates/remote:BUILD.flate2-1.0.24.bazel"),
        )

    if generic_array__0_14_6:
        maybe(
            native.new_local_repository,
            name = "raze__generic_array__0_14_6",
            path = generic_array__0_14_6,
            build_file = "//third_party/rust/crates/remote:BUILD.generic-array-0.14.6.bazel",
        )
    else:
        maybe(
            http_archive,
            name = "raze__generic_array__0_14_6",
            url = "https://crates.io/api/v1/crates/generic-array/0.14.6/download",
            type = "tar.gz",
            sha256 = "bff49e947297f3312447abdca79f45f4738097cc82b06e72054d2223f601f1b9",
            strip_prefix = "generic-array-0.14.6",
            build_file = Label("//third_party/rust/crates/remote:BUILD.generic-array-0.14.6.bazel"),
        )

    if getrandom__0_2_7:
        maybe(
            native.new_local_repository,
            name = "raze__getrandom__0_2_7",
            path = getrandom__0_2_7,
            build_file = "//third_party/rust/crates/remote:BUILD.getrandom-0.2.7.bazel",
        )
    else:
        maybe(
            http_archive,
            name = "raze__getrandom__0_2_7",
            url = "https://crates.io/api/v1/crates/getrandom/0.2.7/download",
            type = "tar.gz",
            sha256 = "4eb1a864a501629691edf6c15a593b7a51eebaa1e8468e9ddc623de7c9b58ec6",
            strip_prefix = "getrandom-0.2.7",
            build_file = Label("//third_party/rust/crates/remote:BUILD.getrandom-0.2.7.bazel"),
        )

    if ghost__0_1_6:
        maybe(
            native.new_local_repository,
            name = "raze__ghost__0_1_6",
            path = ghost__0_1_6,
            build_file = "//third_party/rust/crates/remote:BUILD.ghost-0.1.6.bazel",
        )
    else:
        maybe(
            http_archive,
            name = "raze__ghost__0_1_6",
            url = "https://crates.io/api/v1/crates/ghost/0.1.6/download",
            type = "tar.gz",
            sha256 = "eb19fe8de3ea0920d282f7b77dd4227aea6b8b999b42cdf0ca41b2472b14443a",
            strip_prefix = "ghost-0.1.6",
            build_file = Label("//third_party/rust/crates/remote:BUILD.ghost-0.1.6.bazel"),
        )

    if gimli__0_26_2:
        maybe(
            native.new_local_repository,
            name = "raze__gimli__0_26_2",
            path = gimli__0_26_2,
            build_file = "//third_party/rust/crates/remote:BUILD.gimli-0.26.2.bazel",
        )
    else:
        maybe(
            http_archive,
            name = "raze__gimli__0_26_2",
            url = "https://crates.io/api/v1/crates/gimli/0.26.2/download",
            type = "tar.gz",
            sha256 = "22030e2c5a68ec659fde1e949a745124b48e6fa8b045b7ed5bd1fe4ccc5c4e5d",
            strip_prefix = "gimli-0.26.2",
            build_file = Label("//third_party/rust/crates/remote:BUILD.gimli-0.26.2.bazel"),
        )

    if heck__0_3_3:
        maybe(
            native.new_local_repository,
            name = "raze__heck__0_3_3",
            path = heck__0_3_3,
            build_file = "//third_party/rust/crates/remote:BUILD.heck-0.3.3.bazel",
        )
    else:
        maybe(
            http_archive,
            name = "raze__heck__0_3_3",
            url = "https://crates.io/api/v1/crates/heck/0.3.3/download",
            type = "tar.gz",
            sha256 = "6d621efb26863f0e9924c6ac577e8275e5e6b77455db64ffa6c65c904e9e132c",
            strip_prefix = "heck-0.3.3",
            build_file = Label("//third_party/rust/crates/remote:BUILD.heck-0.3.3.bazel"),
        )

    if hermit_abi__0_1_19:
        maybe(
            native.new_local_repository,
            name = "raze__hermit_abi__0_1_19",
            path = hermit_abi__0_1_19,
            build_file = "//third_party/rust/crates/remote:BUILD.hermit-abi-0.1.19.bazel",
        )
    else:
        maybe(
            http_archive,
            name = "raze__hermit_abi__0_1_19",
            url = "https://crates.io/api/v1/crates/hermit-abi/0.1.19/download",
            type = "tar.gz",
            sha256 = "62b467343b94ba476dcb2500d242dadbb39557df889310ac77c5d99100aaac33",
            strip_prefix = "hermit-abi-0.1.19",
            build_file = Label("//third_party/rust/crates/remote:BUILD.hermit-abi-0.1.19.bazel"),
        )

    if hex__0_4_3:
        maybe(
            native.new_local_repository,
            name = "raze__hex__0_4_3",
            path = hex__0_4_3,
            build_file = "//third_party/rust/crates/remote:BUILD.hex-0.4.3.bazel",
        )
    else:
        maybe(
            http_archive,
            name = "raze__hex__0_4_3",
            url = "https://crates.io/api/v1/crates/hex/0.4.3/download",
            type = "tar.gz",
            sha256 = "7f24254aa9a54b5c858eaee2f5bccdb46aaf0e486a595ed5fd8f86ba55232a70",
            strip_prefix = "hex-0.4.3",
            build_file = Label("//third_party/rust/crates/remote:BUILD.hex-0.4.3.bazel"),
        )

    if humantime__2_1_0:
        maybe(
            native.new_local_repository,
            name = "raze__humantime__2_1_0",
            path = humantime__2_1_0,
            build_file = "//third_party/rust/crates/remote:BUILD.humantime-2.1.0.bazel",
        )
    else:
        maybe(
            http_archive,
            name = "raze__humantime__2_1_0",
            url = "https://crates.io/api/v1/crates/humantime/2.1.0/download",
            type = "tar.gz",
            sha256 = "9a3a5bfb195931eeb336b2a7b4d761daec841b97f947d34394601737a7bba5e4",
            strip_prefix = "humantime-2.1.0",
            build_file = Label("//third_party/rust/crates/remote:BUILD.humantime-2.1.0.bazel"),
        )

    if iana_time_zone__0_1_47:
        maybe(
            native.new_local_repository,
            name = "raze__iana_time_zone__0_1_47",
            path = iana_time_zone__0_1_47,
            build_file = "//third_party/rust/crates/remote:BUILD.iana-time-zone-0.1.47.bazel",
        )
    else:
        maybe(
            http_archive,
            name = "raze__iana_time_zone__0_1_47",
            url = "https://crates.io/api/v1/crates/iana-time-zone/0.1.47/download",
            type = "tar.gz",
            sha256 = "4c495f162af0bf17656d0014a0eded5f3cd2f365fdd204548c2869db89359dc7",
            strip_prefix = "iana-time-zone-0.1.47",
            build_file = Label("//third_party/rust/crates/remote:BUILD.iana-time-zone-0.1.47.bazel"),
        )

    if indicatif__0_16_2:
        maybe(
            native.new_local_repository,
            name = "raze__indicatif__0_16_2",
            path = indicatif__0_16_2,
            build_file = "//third_party/rust/crates/remote:BUILD.indicatif-0.16.2.bazel",
        )
    else:
        maybe(
            http_archive,
            name = "raze__indicatif__0_16_2",
            url = "https://crates.io/api/v1/crates/indicatif/0.16.2/download",
            type = "tar.gz",
            sha256 = "2d207dc617c7a380ab07ff572a6e52fa202a2a8f355860ac9c38e23f8196be1b",
            strip_prefix = "indicatif-0.16.2",
            build_file = Label("//third_party/rust/crates/remote:BUILD.indicatif-0.16.2.bazel"),
        )

    if instant__0_1_12:
        maybe(
            native.new_local_repository,
            name = "raze__instant__0_1_12",
            path = instant__0_1_12,
            build_file = "//third_party/rust/crates/remote:BUILD.instant-0.1.12.bazel",
        )
    else:
        maybe(
            http_archive,
            name = "raze__instant__0_1_12",
            url = "https://crates.io/api/v1/crates/instant/0.1.12/download",
            type = "tar.gz",
            sha256 = "7a5bbe824c507c5da5956355e86a746d82e0e1464f65d862cc5e71da70e94b2c",
            strip_prefix = "instant-0.1.12",
            build_file = Label("//third_party/rust/crates/remote:BUILD.instant-0.1.12.bazel"),
        )

    if inventory__0_2_3:
        maybe(
            native.new_local_repository,
            name = "raze__inventory__0_2_3",
            path = inventory__0_2_3,
            build_file = "//third_party/rust/crates/remote:BUILD.inventory-0.2.3.bazel",
        )
    else:
        maybe(
            http_archive,
            name = "raze__inventory__0_2_3",
            url = "https://crates.io/api/v1/crates/inventory/0.2.3/download",
            type = "tar.gz",
            sha256 = "84344c6e0b90a9e2b6f3f9abe5cc74402684e348df7b32adca28747e0cef091a",
            strip_prefix = "inventory-0.2.3",
            build_file = Label("//third_party/rust/crates/remote:BUILD.inventory-0.2.3.bazel"),
        )

    if itoa__1_0_3:
        maybe(
            native.new_local_repository,
            name = "raze__itoa__1_0_3",
            path = itoa__1_0_3,
            build_file = "//third_party/rust/crates/remote:BUILD.itoa-1.0.3.bazel",
        )
    else:
        maybe(
            http_archive,
            name = "raze__itoa__1_0_3",
            url = "https://crates.io/api/v1/crates/itoa/1.0.3/download",
            type = "tar.gz",
            sha256 = "6c8af84674fe1f223a982c933a0ee1086ac4d4052aa0fb8060c12c6ad838e754",
            strip_prefix = "itoa-1.0.3",
            build_file = Label("//third_party/rust/crates/remote:BUILD.itoa-1.0.3.bazel"),
        )

    if js_sys__0_3_60:
        maybe(
            native.new_local_repository,
            name = "raze__js_sys__0_3_60",
            path = js_sys__0_3_60,
            build_file = "//third_party/rust/crates/remote:BUILD.js-sys-0.3.60.bazel",
        )
    else:
        maybe(
            http_archive,
            name = "raze__js_sys__0_3_60",
            url = "https://crates.io/api/v1/crates/js-sys/0.3.60/download",
            type = "tar.gz",
            sha256 = "49409df3e3bf0856b916e2ceaca09ee28e6871cf7d9ce97a692cacfdb2a25a47",
            strip_prefix = "js-sys-0.3.60",
            build_file = Label("//third_party/rust/crates/remote:BUILD.js-sys-0.3.60.bazel"),
        )

    if lazy_static__1_4_0:
        maybe(
            native.new_local_repository,
            name = "raze__lazy_static__1_4_0",
            path = lazy_static__1_4_0,
            build_file = "//third_party/rust/crates/remote:BUILD.lazy_static-1.4.0.bazel",
        )
    else:
        maybe(
            http_archive,
            name = "raze__lazy_static__1_4_0",
            url = "https://crates.io/api/v1/crates/lazy_static/1.4.0/download",
            type = "tar.gz",
            sha256 = "e2abad23fbc42b3700f2f279844dc832adb2b2eb069b2df918f455c4e18cc646",
            strip_prefix = "lazy_static-1.4.0",
            build_file = Label("//third_party/rust/crates/remote:BUILD.lazy_static-1.4.0.bazel"),
        )

    if libc__0_2_132:
        maybe(
            native.new_local_repository,
            name = "raze__libc__0_2_132",
            path = libc__0_2_132,
            build_file = "//third_party/rust/crates/remote:BUILD.libc-0.2.132.bazel",
        )
    else:
        maybe(
            http_archive,
            name = "raze__libc__0_2_132",
            url = "https://crates.io/api/v1/crates/libc/0.2.132/download",
            type = "tar.gz",
            sha256 = "8371e4e5341c3a96db127eb2465ac681ced4c433e01dd0e938adbef26ba93ba5",
            strip_prefix = "libc-0.2.132",
            build_file = Label("//third_party/rust/crates/remote:BUILD.libc-0.2.132.bazel"),
        )

    if libm__0_2_5:
        maybe(
            native.new_local_repository,
            name = "raze__libm__0_2_5",
            path = libm__0_2_5,
            build_file = "//third_party/rust/crates/remote:BUILD.libm-0.2.5.bazel",
        )
    else:
        maybe(
            http_archive,
            name = "raze__libm__0_2_5",
            url = "https://crates.io/api/v1/crates/libm/0.2.5/download",
            type = "tar.gz",
            sha256 = "292a948cd991e376cf75541fe5b97a1081d713c618b4f1b9500f8844e49eb565",
            strip_prefix = "libm-0.2.5",
            build_file = Label("//third_party/rust/crates/remote:BUILD.libm-0.2.5.bazel"),
        )

    if libudev__0_3_0:
        maybe(
            native.new_local_repository,
            name = "raze__libudev__0_3_0",
            path = libudev__0_3_0,
            build_file = "//third_party/rust/crates/remote:BUILD.libudev-0.3.0.bazel",
        )
    else:
        maybe(
            http_archive,
            name = "raze__libudev__0_3_0",
            url = "https://crates.io/api/v1/crates/libudev/0.3.0/download",
            type = "tar.gz",
            sha256 = "78b324152da65df7bb95acfcaab55e3097ceaab02fb19b228a9eb74d55f135e0",
            strip_prefix = "libudev-0.3.0",
            build_file = Label("//third_party/rust/crates/remote:BUILD.libudev-0.3.0.bazel"),
        )

    if libudev_sys__0_1_4:
        maybe(
            native.new_local_repository,
            name = "raze__libudev_sys__0_1_4",
            path = libudev_sys__0_1_4,
            build_file = "//third_party/rust/crates/remote:BUILD.libudev-sys-0.1.4.bazel",
        )
    else:
        maybe(
            http_archive,
            name = "raze__libudev_sys__0_1_4",
            url = "https://crates.io/api/v1/crates/libudev-sys/0.1.4/download",
            type = "tar.gz",
            sha256 = "3c8469b4a23b962c1396b9b451dda50ef5b283e8dd309d69033475fa9b334324",
            strip_prefix = "libudev-sys-0.1.4",
        patches = [
            "@//third_party/rust/crates/patches:libudev-sys-0.1.4.patch",
        ],
        patch_args = [
            "-p1",
        ],
            build_file = Label("//third_party/rust/crates/remote:BUILD.libudev-sys-0.1.4.bazel"),
        )

    if libusb1_sys__0_5_0:
        maybe(
            native.new_local_repository,
            name = "raze__libusb1_sys__0_5_0",
            path = libusb1_sys__0_5_0,
            build_file = "//third_party/rust/crates/remote:BUILD.libusb1-sys-0.5.0.bazel",
        )
    else:
        maybe(
            http_archive,
            name = "raze__libusb1_sys__0_5_0",
            url = "https://crates.io/api/v1/crates/libusb1-sys/0.5.0/download",
            type = "tar.gz",
            sha256 = "e22e89d08bbe6816c6c5d446203b859eba35b8fa94bf1b7edb2f6d25d43f023f",
            strip_prefix = "libusb1-sys-0.5.0",
            build_file = Label("//third_party/rust/crates/remote:BUILD.libusb1-sys-0.5.0.bazel"),
        )

    if log__0_4_17:
        maybe(
            native.new_local_repository,
            name = "raze__log__0_4_17",
            path = log__0_4_17,
            build_file = "//third_party/rust/crates/remote:BUILD.log-0.4.17.bazel",
        )
    else:
        maybe(
            http_archive,
            name = "raze__log__0_4_17",
            url = "https://crates.io/api/v1/crates/log/0.4.17/download",
            type = "tar.gz",
            sha256 = "abb12e687cfb44aa40f41fc3978ef76448f9b6038cad6aef4259d3c095a2382e",
            strip_prefix = "log-0.4.17",
            build_file = Label("//third_party/rust/crates/remote:BUILD.log-0.4.17.bazel"),
        )

    if mach__0_1_2:
        maybe(
            native.new_local_repository,
            name = "raze__mach__0_1_2",
            path = mach__0_1_2,
            build_file = "//third_party/rust/crates/remote:BUILD.mach-0.1.2.bazel",
        )
    else:
        maybe(
            http_archive,
            name = "raze__mach__0_1_2",
            url = "https://crates.io/api/v1/crates/mach/0.1.2/download",
            type = "tar.gz",
            sha256 = "2fd13ee2dd61cc82833ba05ade5a30bb3d63f7ced605ef827063c63078302de9",
            strip_prefix = "mach-0.1.2",
            build_file = Label("//third_party/rust/crates/remote:BUILD.mach-0.1.2.bazel"),
        )

    if mach__0_3_2:
        maybe(
            native.new_local_repository,
            name = "raze__mach__0_3_2",
            path = mach__0_3_2,
            build_file = "//third_party/rust/crates/remote:BUILD.mach-0.3.2.bazel",
        )
    else:
        maybe(
            http_archive,
            name = "raze__mach__0_3_2",
            url = "https://crates.io/api/v1/crates/mach/0.3.2/download",
            type = "tar.gz",
            sha256 = "b823e83b2affd8f40a9ee8c29dbc56404c1e34cd2710921f2801e2cf29527afa",
            strip_prefix = "mach-0.3.2",
            build_file = Label("//third_party/rust/crates/remote:BUILD.mach-0.3.2.bazel"),
        )

    if memchr__2_5_0:
        maybe(
            native.new_local_repository,
            name = "raze__memchr__2_5_0",
            path = memchr__2_5_0,
            build_file = "//third_party/rust/crates/remote:BUILD.memchr-2.5.0.bazel",
        )
    else:
        maybe(
            http_archive,
            name = "raze__memchr__2_5_0",
            url = "https://crates.io/api/v1/crates/memchr/2.5.0/download",
            type = "tar.gz",
            sha256 = "2dffe52ecf27772e601905b7522cb4ef790d2cc203488bbd0e2fe85fcb74566d",
            strip_prefix = "memchr-2.5.0",
            build_file = Label("//third_party/rust/crates/remote:BUILD.memchr-2.5.0.bazel"),
        )

    if memoffset__0_6_5:
        maybe(
            native.new_local_repository,
            name = "raze__memoffset__0_6_5",
            path = memoffset__0_6_5,
            build_file = "//third_party/rust/crates/remote:BUILD.memoffset-0.6.5.bazel",
        )
    else:
        maybe(
            http_archive,
            name = "raze__memoffset__0_6_5",
            url = "https://crates.io/api/v1/crates/memoffset/0.6.5/download",
            type = "tar.gz",
            sha256 = "5aa361d4faea93603064a027415f07bd8e1d5c88c9fbf68bf56a285428fd79ce",
            strip_prefix = "memoffset-0.6.5",
            build_file = Label("//third_party/rust/crates/remote:BUILD.memoffset-0.6.5.bazel"),
        )

    if miniz_oxide__0_5_4:
        maybe(
            native.new_local_repository,
            name = "raze__miniz_oxide__0_5_4",
            path = miniz_oxide__0_5_4,
            build_file = "//third_party/rust/crates/remote:BUILD.miniz_oxide-0.5.4.bazel",
        )
    else:
        maybe(
            http_archive,
            name = "raze__miniz_oxide__0_5_4",
            url = "https://crates.io/api/v1/crates/miniz_oxide/0.5.4/download",
            type = "tar.gz",
            sha256 = "96590ba8f175222643a85693f33d26e9c8a015f599c216509b1a6894af675d34",
            strip_prefix = "miniz_oxide-0.5.4",
            build_file = Label("//third_party/rust/crates/remote:BUILD.miniz_oxide-0.5.4.bazel"),
        )

    if mio__0_7_14:
        maybe(
            native.new_local_repository,
            name = "raze__mio__0_7_14",
            path = mio__0_7_14,
            build_file = "//third_party/rust/crates/remote:BUILD.mio-0.7.14.bazel",
        )
    else:
        maybe(
            http_archive,
            name = "raze__mio__0_7_14",
            url = "https://crates.io/api/v1/crates/mio/0.7.14/download",
            type = "tar.gz",
            sha256 = "8067b404fe97c70829f082dec8bcf4f71225d7eaea1d8645349cb76fa06205cc",
            strip_prefix = "mio-0.7.14",
            build_file = Label("//third_party/rust/crates/remote:BUILD.mio-0.7.14.bazel"),
        )

    if mio_signals__0_1_5:
        maybe(
            native.new_local_repository,
            name = "raze__mio_signals__0_1_5",
            path = mio_signals__0_1_5,
            build_file = "//third_party/rust/crates/remote:BUILD.mio-signals-0.1.5.bazel",
        )
    else:
        maybe(
            http_archive,
            name = "raze__mio_signals__0_1_5",
            url = "https://crates.io/api/v1/crates/mio-signals/0.1.5/download",
            type = "tar.gz",
            sha256 = "119701964987706f4147cff32b09ae64019be6417a90fda6f96cfac0348e8b79",
            strip_prefix = "mio-signals-0.1.5",
            build_file = Label("//third_party/rust/crates/remote:BUILD.mio-signals-0.1.5.bazel"),
        )

    if miow__0_3_7:
        maybe(
            native.new_local_repository,
            name = "raze__miow__0_3_7",
            path = miow__0_3_7,
            build_file = "//third_party/rust/crates/remote:BUILD.miow-0.3.7.bazel",
        )
    else:
        maybe(
            http_archive,
            name = "raze__miow__0_3_7",
            url = "https://crates.io/api/v1/crates/miow/0.3.7/download",
            type = "tar.gz",
            sha256 = "b9f1c5b025cda876f66ef43a113f91ebc9f4ccef34843000e0adf6ebbab84e21",
            strip_prefix = "miow-0.3.7",
            build_file = Label("//third_party/rust/crates/remote:BUILD.miow-0.3.7.bazel"),
        )

    if nix__0_17_0:
        maybe(
            native.new_local_repository,
            name = "raze__nix__0_17_0",
            path = nix__0_17_0,
            build_file = "//third_party/rust/crates/remote:BUILD.nix-0.17.0.bazel",
        )
    else:
        maybe(
            http_archive,
            name = "raze__nix__0_17_0",
            url = "https://crates.io/api/v1/crates/nix/0.17.0/download",
            type = "tar.gz",
            sha256 = "50e4785f2c3b7589a0d0c1dd60285e1188adac4006e8abd6dd578e1567027363",
            strip_prefix = "nix-0.17.0",
            build_file = Label("//third_party/rust/crates/remote:BUILD.nix-0.17.0.bazel"),
        )

    if nix__0_24_2:
        maybe(
            native.new_local_repository,
            name = "raze__nix__0_24_2",
            path = nix__0_24_2,
            build_file = "//third_party/rust/crates/remote:BUILD.nix-0.24.2.bazel",
        )
    else:
        maybe(
            http_archive,
            name = "raze__nix__0_24_2",
            url = "https://crates.io/api/v1/crates/nix/0.24.2/download",
            type = "tar.gz",
            sha256 = "195cdbc1741b8134346d515b3a56a1c94b0912758009cfd53f99ea0f57b065fc",
            strip_prefix = "nix-0.24.2",
            build_file = Label("//third_party/rust/crates/remote:BUILD.nix-0.24.2.bazel"),
        )

    if ntapi__0_3_7:
        maybe(
            native.new_local_repository,
            name = "raze__ntapi__0_3_7",
            path = ntapi__0_3_7,
            build_file = "//third_party/rust/crates/remote:BUILD.ntapi-0.3.7.bazel",
        )
    else:
        maybe(
            http_archive,
            name = "raze__ntapi__0_3_7",
            url = "https://crates.io/api/v1/crates/ntapi/0.3.7/download",
            type = "tar.gz",
            sha256 = "c28774a7fd2fbb4f0babd8237ce554b73af68021b5f695a3cebd6c59bac0980f",
            strip_prefix = "ntapi-0.3.7",
            build_file = Label("//third_party/rust/crates/remote:BUILD.ntapi-0.3.7.bazel"),
        )

    if num_bigint_dig__0_7_0:
        maybe(
            native.new_local_repository,
            name = "raze__num_bigint_dig__0_7_0",
            path = num_bigint_dig__0_7_0,
            build_file = "//third_party/rust/crates/remote:BUILD.num-bigint-dig-0.7.0.bazel",
        )
    else:
        maybe(
            http_archive,
            name = "raze__num_bigint_dig__0_7_0",
            url = "https://crates.io/api/v1/crates/num-bigint-dig/0.7.0/download",
            type = "tar.gz",
            sha256 = "4547ee5541c18742396ae2c895d0717d0f886d8823b8399cdaf7b07d63ad0480",
            strip_prefix = "num-bigint-dig-0.7.0",
            build_file = Label("//third_party/rust/crates/remote:BUILD.num-bigint-dig-0.7.0.bazel"),
        )

    if num_integer__0_1_45:
        maybe(
            native.new_local_repository,
            name = "raze__num_integer__0_1_45",
            path = num_integer__0_1_45,
            build_file = "//third_party/rust/crates/remote:BUILD.num-integer-0.1.45.bazel",
        )
    else:
        maybe(
            http_archive,
            name = "raze__num_integer__0_1_45",
            url = "https://crates.io/api/v1/crates/num-integer/0.1.45/download",
            type = "tar.gz",
            sha256 = "225d3389fb3509a24c93f5c29eb6bde2586b98d9f016636dff58d7c6f7569cd9",
            strip_prefix = "num-integer-0.1.45",
            build_file = Label("//third_party/rust/crates/remote:BUILD.num-integer-0.1.45.bazel"),
        )

    if num_iter__0_1_43:
        maybe(
            native.new_local_repository,
            name = "raze__num_iter__0_1_43",
            path = num_iter__0_1_43,
            build_file = "//third_party/rust/crates/remote:BUILD.num-iter-0.1.43.bazel",
        )
    else:
        maybe(
            http_archive,
            name = "raze__num_iter__0_1_43",
            url = "https://crates.io/api/v1/crates/num-iter/0.1.43/download",
            type = "tar.gz",
            sha256 = "7d03e6c028c5dc5cac6e2dec0efda81fc887605bb3d884578bb6d6bf7514e252",
            strip_prefix = "num-iter-0.1.43",
            build_file = Label("//third_party/rust/crates/remote:BUILD.num-iter-0.1.43.bazel"),
        )

    if num_traits__0_2_15:
        maybe(
            native.new_local_repository,
            name = "raze__num_traits__0_2_15",
            path = num_traits__0_2_15,
            build_file = "//third_party/rust/crates/remote:BUILD.num-traits-0.2.15.bazel",
        )
    else:
        maybe(
            http_archive,
            name = "raze__num_traits__0_2_15",
            url = "https://crates.io/api/v1/crates/num-traits/0.2.15/download",
            type = "tar.gz",
            sha256 = "578ede34cf02f8924ab9447f50c28075b4d3e5b269972345e7e0372b38c6cdcd",
            strip_prefix = "num-traits-0.2.15",
            build_file = Label("//third_party/rust/crates/remote:BUILD.num-traits-0.2.15.bazel"),
        )

    if num_enum__0_5_7:
        maybe(
            native.new_local_repository,
            name = "raze__num_enum__0_5_7",
            path = num_enum__0_5_7,
            build_file = "//third_party/rust/crates/remote:BUILD.num_enum-0.5.7.bazel",
        )
    else:
        maybe(
            http_archive,
            name = "raze__num_enum__0_5_7",
            url = "https://crates.io/api/v1/crates/num_enum/0.5.7/download",
            type = "tar.gz",
            sha256 = "cf5395665662ef45796a4ff5486c5d41d29e0c09640af4c5f17fd94ee2c119c9",
            strip_prefix = "num_enum-0.5.7",
            build_file = Label("//third_party/rust/crates/remote:BUILD.num_enum-0.5.7.bazel"),
        )

    if num_enum_derive__0_5_7:
        maybe(
            native.new_local_repository,
            name = "raze__num_enum_derive__0_5_7",
            path = num_enum_derive__0_5_7,
            build_file = "//third_party/rust/crates/remote:BUILD.num_enum_derive-0.5.7.bazel",
        )
    else:
        maybe(
            http_archive,
            name = "raze__num_enum_derive__0_5_7",
            url = "https://crates.io/api/v1/crates/num_enum_derive/0.5.7/download",
            type = "tar.gz",
            sha256 = "3b0498641e53dd6ac1a4f22547548caa6864cc4933784319cd1775271c5a46ce",
            strip_prefix = "num_enum_derive-0.5.7",
            build_file = Label("//third_party/rust/crates/remote:BUILD.num_enum_derive-0.5.7.bazel"),
        )

    if number_prefix__0_4_0:
        maybe(
            native.new_local_repository,
            name = "raze__number_prefix__0_4_0",
            path = number_prefix__0_4_0,
            build_file = "//third_party/rust/crates/remote:BUILD.number_prefix-0.4.0.bazel",
        )
    else:
        maybe(
            http_archive,
            name = "raze__number_prefix__0_4_0",
            url = "https://crates.io/api/v1/crates/number_prefix/0.4.0/download",
            type = "tar.gz",
            sha256 = "830b246a0e5f20af87141b25c173cd1b609bd7779a4617d6ec582abaf90870f3",
            strip_prefix = "number_prefix-0.4.0",
            build_file = Label("//third_party/rust/crates/remote:BUILD.number_prefix-0.4.0.bazel"),
        )

    if object__0_25_3:
        maybe(
            native.new_local_repository,
            name = "raze__object__0_25_3",
            path = object__0_25_3,
            build_file = "//third_party/rust/crates/remote:BUILD.object-0.25.3.bazel",
        )
    else:
        maybe(
            http_archive,
            name = "raze__object__0_25_3",
            url = "https://crates.io/api/v1/crates/object/0.25.3/download",
            type = "tar.gz",
            sha256 = "a38f2be3697a57b4060074ff41b44c16870d916ad7877c17696e063257482bc7",
            strip_prefix = "object-0.25.3",
            build_file = Label("//third_party/rust/crates/remote:BUILD.object-0.25.3.bazel"),
        )

    if object__0_29_0:
        maybe(
            native.new_local_repository,
            name = "raze__object__0_29_0",
            path = object__0_29_0,
            build_file = "//third_party/rust/crates/remote:BUILD.object-0.29.0.bazel",
        )
    else:
        maybe(
            http_archive,
            name = "raze__object__0_29_0",
            url = "https://crates.io/api/v1/crates/object/0.29.0/download",
            type = "tar.gz",
            sha256 = "21158b2c33aa6d4561f1c0a6ea283ca92bc54802a93b263e910746d679a7eb53",
            strip_prefix = "object-0.29.0",
            build_file = Label("//third_party/rust/crates/remote:BUILD.object-0.29.0.bazel"),
        )

    if once_cell__1_14_0:
        maybe(
            native.new_local_repository,
            name = "raze__once_cell__1_14_0",
            path = once_cell__1_14_0,
            build_file = "//third_party/rust/crates/remote:BUILD.once_cell-1.14.0.bazel",
        )
    else:
        maybe(
            http_archive,
            name = "raze__once_cell__1_14_0",
            url = "https://crates.io/api/v1/crates/once_cell/1.14.0/download",
            type = "tar.gz",
            sha256 = "2f7254b99e31cad77da24b08ebf628882739a608578bb1bcdfc1f9c21260d7c0",
            strip_prefix = "once_cell-1.14.0",
            build_file = Label("//third_party/rust/crates/remote:BUILD.once_cell-1.14.0.bazel"),
        )

    if pem_rfc7468__0_2_4:
        maybe(
            native.new_local_repository,
            name = "raze__pem_rfc7468__0_2_4",
            path = pem_rfc7468__0_2_4,
            build_file = "//third_party/rust/crates/remote:BUILD.pem-rfc7468-0.2.4.bazel",
        )
    else:
        maybe(
            http_archive,
            name = "raze__pem_rfc7468__0_2_4",
            url = "https://crates.io/api/v1/crates/pem-rfc7468/0.2.4/download",
            type = "tar.gz",
            sha256 = "84e93a3b1cc0510b03020f33f21e62acdde3dcaef432edc95bea377fbd4c2cd4",
            strip_prefix = "pem-rfc7468-0.2.4",
            build_file = Label("//third_party/rust/crates/remote:BUILD.pem-rfc7468-0.2.4.bazel"),
        )

    if pkcs1__0_2_4:
        maybe(
            native.new_local_repository,
            name = "raze__pkcs1__0_2_4",
            path = pkcs1__0_2_4,
            build_file = "//third_party/rust/crates/remote:BUILD.pkcs1-0.2.4.bazel",
        )
    else:
        maybe(
            http_archive,
            name = "raze__pkcs1__0_2_4",
            url = "https://crates.io/api/v1/crates/pkcs1/0.2.4/download",
            type = "tar.gz",
            sha256 = "116bee8279d783c0cf370efa1a94632f2108e5ef0bb32df31f051647810a4e2c",
            strip_prefix = "pkcs1-0.2.4",
            build_file = Label("//third_party/rust/crates/remote:BUILD.pkcs1-0.2.4.bazel"),
        )

    if pkcs8__0_7_6:
        maybe(
            native.new_local_repository,
            name = "raze__pkcs8__0_7_6",
            path = pkcs8__0_7_6,
            build_file = "//third_party/rust/crates/remote:BUILD.pkcs8-0.7.6.bazel",
        )
    else:
        maybe(
            http_archive,
            name = "raze__pkcs8__0_7_6",
            url = "https://crates.io/api/v1/crates/pkcs8/0.7.6/download",
            type = "tar.gz",
            sha256 = "ee3ef9b64d26bad0536099c816c6734379e45bbd5f14798def6809e5cc350447",
            strip_prefix = "pkcs8-0.7.6",
            build_file = Label("//third_party/rust/crates/remote:BUILD.pkcs8-0.7.6.bazel"),
        )

    if pkg_config__0_3_25:
        maybe(
            native.new_local_repository,
            name = "raze__pkg_config__0_3_25",
            path = pkg_config__0_3_25,
            build_file = "//third_party/rust/crates/remote:BUILD.pkg-config-0.3.25.bazel",
        )
    else:
        maybe(
            http_archive,
            name = "raze__pkg_config__0_3_25",
            url = "https://crates.io/api/v1/crates/pkg-config/0.3.25/download",
            type = "tar.gz",
            sha256 = "1df8c4ec4b0627e53bdf214615ad287367e482558cf84b109250b37464dc03ae",
            strip_prefix = "pkg-config-0.3.25",
            build_file = Label("//third_party/rust/crates/remote:BUILD.pkg-config-0.3.25.bazel"),
        )

    if ppv_lite86__0_2_16:
        maybe(
            native.new_local_repository,
            name = "raze__ppv_lite86__0_2_16",
            path = ppv_lite86__0_2_16,
            build_file = "//third_party/rust/crates/remote:BUILD.ppv-lite86-0.2.16.bazel",
        )
    else:
        maybe(
            http_archive,
            name = "raze__ppv_lite86__0_2_16",
            url = "https://crates.io/api/v1/crates/ppv-lite86/0.2.16/download",
            type = "tar.gz",
            sha256 = "eb9f9e6e233e5c4a35559a617bf40a4ec447db2e84c20b55a6f83167b7e57872",
            strip_prefix = "ppv-lite86-0.2.16",
            build_file = Label("//third_party/rust/crates/remote:BUILD.ppv-lite86-0.2.16.bazel"),
        )

    if proc_macro_crate__1_2_1:
        maybe(
            native.new_local_repository,
            name = "raze__proc_macro_crate__1_2_1",
            path = proc_macro_crate__1_2_1,
            build_file = "//third_party/rust/crates/remote:BUILD.proc-macro-crate-1.2.1.bazel",
        )
    else:
        maybe(
            http_archive,
            name = "raze__proc_macro_crate__1_2_1",
            url = "https://crates.io/api/v1/crates/proc-macro-crate/1.2.1/download",
            type = "tar.gz",
            sha256 = "eda0fc3b0fb7c975631757e14d9049da17374063edb6ebbcbc54d880d4fe94e9",
            strip_prefix = "proc-macro-crate-1.2.1",
            build_file = Label("//third_party/rust/crates/remote:BUILD.proc-macro-crate-1.2.1.bazel"),
        )

    if proc_macro_error__1_0_4:
        maybe(
            native.new_local_repository,
            name = "raze__proc_macro_error__1_0_4",
            path = proc_macro_error__1_0_4,
            build_file = "//third_party/rust/crates/remote:BUILD.proc-macro-error-1.0.4.bazel",
        )
    else:
        maybe(
            http_archive,
            name = "raze__proc_macro_error__1_0_4",
            url = "https://crates.io/api/v1/crates/proc-macro-error/1.0.4/download",
            type = "tar.gz",
            sha256 = "da25490ff9892aab3fcf7c36f08cfb902dd3e71ca0f9f9517bea02a73a5ce38c",
            strip_prefix = "proc-macro-error-1.0.4",
            build_file = Label("//third_party/rust/crates/remote:BUILD.proc-macro-error-1.0.4.bazel"),
        )

    if proc_macro_error_attr__1_0_4:
        maybe(
            native.new_local_repository,
            name = "raze__proc_macro_error_attr__1_0_4",
            path = proc_macro_error_attr__1_0_4,
            build_file = "//third_party/rust/crates/remote:BUILD.proc-macro-error-attr-1.0.4.bazel",
        )
    else:
        maybe(
            http_archive,
            name = "raze__proc_macro_error_attr__1_0_4",
            url = "https://crates.io/api/v1/crates/proc-macro-error-attr/1.0.4/download",
            type = "tar.gz",
            sha256 = "a1be40180e52ecc98ad80b184934baf3d0d29f979574e439af5a55274b35f869",
            strip_prefix = "proc-macro-error-attr-1.0.4",
            build_file = Label("//third_party/rust/crates/remote:BUILD.proc-macro-error-attr-1.0.4.bazel"),
        )

    if proc_macro2__0_4_30:
        maybe(
            native.new_local_repository,
            name = "raze__proc_macro2__0_4_30",
            path = proc_macro2__0_4_30,
            build_file = "//third_party/rust/crates/remote:BUILD.proc-macro2-0.4.30.bazel",
        )
    else:
        maybe(
            http_archive,
            name = "raze__proc_macro2__0_4_30",
            url = "https://crates.io/api/v1/crates/proc-macro2/0.4.30/download",
            type = "tar.gz",
            sha256 = "cf3d2011ab5c909338f7887f4fc896d35932e29146c12c8d01da6b22a80ba759",
            strip_prefix = "proc-macro2-0.4.30",
            build_file = Label("//third_party/rust/crates/remote:BUILD.proc-macro2-0.4.30.bazel"),
        )

    if proc_macro2__1_0_43:
        maybe(
            native.new_local_repository,
            name = "raze__proc_macro2__1_0_43",
            path = proc_macro2__1_0_43,
            build_file = "//third_party/rust/crates/remote:BUILD.proc-macro2-1.0.43.bazel",
        )
    else:
        maybe(
            http_archive,
            name = "raze__proc_macro2__1_0_43",
            url = "https://crates.io/api/v1/crates/proc-macro2/1.0.43/download",
            type = "tar.gz",
            sha256 = "0a2ca2c61bc9f3d74d2886294ab7b9853abd9c1ad903a3ac7815c58989bb7bab",
            strip_prefix = "proc-macro2-1.0.43",
            build_file = Label("//third_party/rust/crates/remote:BUILD.proc-macro2-1.0.43.bazel"),
        )

    if quote__0_6_13:
        maybe(
            native.new_local_repository,
            name = "raze__quote__0_6_13",
            path = quote__0_6_13,
            build_file = "//third_party/rust/crates/remote:BUILD.quote-0.6.13.bazel",
        )
    else:
        maybe(
            http_archive,
            name = "raze__quote__0_6_13",
            url = "https://crates.io/api/v1/crates/quote/0.6.13/download",
            type = "tar.gz",
            sha256 = "6ce23b6b870e8f94f81fb0a363d65d86675884b34a09043c81e5562f11c1f8e1",
            strip_prefix = "quote-0.6.13",
            build_file = Label("//third_party/rust/crates/remote:BUILD.quote-0.6.13.bazel"),
        )

    if quote__1_0_21:
        maybe(
            native.new_local_repository,
            name = "raze__quote__1_0_21",
            path = quote__1_0_21,
            build_file = "//third_party/rust/crates/remote:BUILD.quote-1.0.21.bazel",
        )
    else:
        maybe(
            http_archive,
            name = "raze__quote__1_0_21",
            url = "https://crates.io/api/v1/crates/quote/1.0.21/download",
            type = "tar.gz",
            sha256 = "bbe448f377a7d6961e30f5955f9b8d106c3f5e449d493ee1b125c1d43c2b5179",
            strip_prefix = "quote-1.0.21",
            build_file = Label("//third_party/rust/crates/remote:BUILD.quote-1.0.21.bazel"),
        )

    if rand__0_8_5:
        maybe(
            native.new_local_repository,
            name = "raze__rand__0_8_5",
            path = rand__0_8_5,
            build_file = "//third_party/rust/crates/remote:BUILD.rand-0.8.5.bazel",
        )
    else:
        maybe(
            http_archive,
            name = "raze__rand__0_8_5",
            url = "https://crates.io/api/v1/crates/rand/0.8.5/download",
            type = "tar.gz",
            sha256 = "34af8d1a0e25924bc5b7c43c079c942339d8f0a8b57c39049bef581b46327404",
            strip_prefix = "rand-0.8.5",
            build_file = Label("//third_party/rust/crates/remote:BUILD.rand-0.8.5.bazel"),
        )

    if rand_chacha__0_3_1:
        maybe(
            native.new_local_repository,
            name = "raze__rand_chacha__0_3_1",
            path = rand_chacha__0_3_1,
            build_file = "//third_party/rust/crates/remote:BUILD.rand_chacha-0.3.1.bazel",
        )
    else:
        maybe(
            http_archive,
            name = "raze__rand_chacha__0_3_1",
            url = "https://crates.io/api/v1/crates/rand_chacha/0.3.1/download",
            type = "tar.gz",
            sha256 = "e6c10a63a0fa32252be49d21e7709d4d4baf8d231c2dbce1eaa8141b9b127d88",
            strip_prefix = "rand_chacha-0.3.1",
            build_file = Label("//third_party/rust/crates/remote:BUILD.rand_chacha-0.3.1.bazel"),
        )

    if rand_core__0_6_3:
        maybe(
            native.new_local_repository,
            name = "raze__rand_core__0_6_3",
            path = rand_core__0_6_3,
            build_file = "//third_party/rust/crates/remote:BUILD.rand_core-0.6.3.bazel",
        )
    else:
        maybe(
            http_archive,
            name = "raze__rand_core__0_6_3",
            url = "https://crates.io/api/v1/crates/rand_core/0.6.3/download",
            type = "tar.gz",
            sha256 = "d34f1408f55294453790c48b2f1ebbb1c5b4b7563eb1f418bcfcfdbb06ebb4e7",
            strip_prefix = "rand_core-0.6.3",
            build_file = Label("//third_party/rust/crates/remote:BUILD.rand_core-0.6.3.bazel"),
        )

    if raw_tty__0_1_0:
        maybe(
            native.new_local_repository,
            name = "raze__raw_tty__0_1_0",
            path = raw_tty__0_1_0,
            build_file = "//third_party/rust/crates/remote:BUILD.raw_tty-0.1.0.bazel",
        )
    else:
        maybe(
            http_archive,
            name = "raze__raw_tty__0_1_0",
            url = "https://crates.io/api/v1/crates/raw_tty/0.1.0/download",
            type = "tar.gz",
            sha256 = "51f512d7504049ef0d3f5d48d8aa5129beaea4fccfaf5c500c9b60101394f8b1",
            strip_prefix = "raw_tty-0.1.0",
            build_file = Label("//third_party/rust/crates/remote:BUILD.raw_tty-0.1.0.bazel"),
        )

    if redox_syscall__0_2_16:
        maybe(
            native.new_local_repository,
            name = "raze__redox_syscall__0_2_16",
            path = redox_syscall__0_2_16,
            build_file = "//third_party/rust/crates/remote:BUILD.redox_syscall-0.2.16.bazel",
        )
    else:
        maybe(
            http_archive,
            name = "raze__redox_syscall__0_2_16",
            url = "https://crates.io/api/v1/crates/redox_syscall/0.2.16/download",
            type = "tar.gz",
            sha256 = "fb5a58c1855b4b6819d59012155603f0b22ad30cad752600aadfcb695265519a",
            strip_prefix = "redox_syscall-0.2.16",
            build_file = Label("//third_party/rust/crates/remote:BUILD.redox_syscall-0.2.16.bazel"),
        )

    if redox_users__0_4_3:
        maybe(
            native.new_local_repository,
            name = "raze__redox_users__0_4_3",
            path = redox_users__0_4_3,
            build_file = "//third_party/rust/crates/remote:BUILD.redox_users-0.4.3.bazel",
        )
    else:
        maybe(
            http_archive,
            name = "raze__redox_users__0_4_3",
            url = "https://crates.io/api/v1/crates/redox_users/0.4.3/download",
            type = "tar.gz",
            sha256 = "b033d837a7cf162d7993aded9304e30a83213c648b6e389db233191f891e5c2b",
            strip_prefix = "redox_users-0.4.3",
            build_file = Label("//third_party/rust/crates/remote:BUILD.redox_users-0.4.3.bazel"),
        )

    if regex__1_6_0:
        maybe(
            native.new_local_repository,
            name = "raze__regex__1_6_0",
            path = regex__1_6_0,
            build_file = "//third_party/rust/crates/remote:BUILD.regex-1.6.0.bazel",
        )
    else:
        maybe(
            http_archive,
            name = "raze__regex__1_6_0",
            url = "https://crates.io/api/v1/crates/regex/1.6.0/download",
            type = "tar.gz",
            sha256 = "4c4eb3267174b8c6c2f654116623910a0fef09c4753f8dd83db29c48a0df988b",
            strip_prefix = "regex-1.6.0",
            build_file = Label("//third_party/rust/crates/remote:BUILD.regex-1.6.0.bazel"),
        )

    if regex_syntax__0_6_27:
        maybe(
            native.new_local_repository,
            name = "raze__regex_syntax__0_6_27",
            path = regex_syntax__0_6_27,
            build_file = "//third_party/rust/crates/remote:BUILD.regex-syntax-0.6.27.bazel",
        )
    else:
        maybe(
            http_archive,
            name = "raze__regex_syntax__0_6_27",
            url = "https://crates.io/api/v1/crates/regex-syntax/0.6.27/download",
            type = "tar.gz",
            sha256 = "a3f87b73ce11b1619a3c6332f45341e0047173771e8b8b73f87bfeefb7b56244",
            strip_prefix = "regex-syntax-0.6.27",
            build_file = Label("//third_party/rust/crates/remote:BUILD.regex-syntax-0.6.27.bazel"),
        )

    if remove_dir_all__0_5_3:
        maybe(
            native.new_local_repository,
            name = "raze__remove_dir_all__0_5_3",
            path = remove_dir_all__0_5_3,
            build_file = "//third_party/rust/crates/remote:BUILD.remove_dir_all-0.5.3.bazel",
        )
    else:
        maybe(
            http_archive,
            name = "raze__remove_dir_all__0_5_3",
            url = "https://crates.io/api/v1/crates/remove_dir_all/0.5.3/download",
            type = "tar.gz",
            sha256 = "3acd125665422973a33ac9d3dd2df85edad0f4ae9b00dafb1a05e43a9f5ef8e7",
            strip_prefix = "remove_dir_all-0.5.3",
            build_file = Label("//third_party/rust/crates/remote:BUILD.remove_dir_all-0.5.3.bazel"),
        )

    if rsa__0_5_0:
        maybe(
            native.new_local_repository,
            name = "raze__rsa__0_5_0",
            path = rsa__0_5_0,
            build_file = "//third_party/rust/crates/remote:BUILD.rsa-0.5.0.bazel",
        )
    else:
        maybe(
            http_archive,
            name = "raze__rsa__0_5_0",
            url = "https://crates.io/api/v1/crates/rsa/0.5.0/download",
            type = "tar.gz",
            sha256 = "e05c2603e2823634ab331437001b411b9ed11660fbc4066f3908c84a9439260d",
            strip_prefix = "rsa-0.5.0",
            build_file = Label("//third_party/rust/crates/remote:BUILD.rsa-0.5.0.bazel"),
        )

    if rusb__0_8_1:
        maybe(
            native.new_local_repository,
            name = "raze__rusb__0_8_1",
            path = rusb__0_8_1,
            build_file = "//third_party/rust/crates/remote:BUILD.rusb-0.8.1.bazel",
        )
    else:
        maybe(
            http_archive,
            name = "raze__rusb__0_8_1",
            url = "https://crates.io/api/v1/crates/rusb/0.8.1/download",
            type = "tar.gz",
            sha256 = "d9a5084628cc5be77b1c750b3e5ee0cc519d2f2491b3f06b78b3aac3328b00ad",
            strip_prefix = "rusb-0.8.1",
            build_file = Label("//third_party/rust/crates/remote:BUILD.rusb-0.8.1.bazel"),
        )

    if rustc_demangle__0_1_21:
        maybe(
            native.new_local_repository,
            name = "raze__rustc_demangle__0_1_21",
            path = rustc_demangle__0_1_21,
            build_file = "//third_party/rust/crates/remote:BUILD.rustc-demangle-0.1.21.bazel",
        )
    else:
        maybe(
            http_archive,
            name = "raze__rustc_demangle__0_1_21",
            url = "https://crates.io/api/v1/crates/rustc-demangle/0.1.21/download",
            type = "tar.gz",
            sha256 = "7ef03e0a2b150c7a90d01faf6254c9c48a41e95fb2a8c2ac1c6f0d2b9aefc342",
            strip_prefix = "rustc-demangle-0.1.21",
            build_file = Label("//third_party/rust/crates/remote:BUILD.rustc-demangle-0.1.21.bazel"),
        )

    if rustc_version__0_2_3:
        maybe(
            native.new_local_repository,
            name = "raze__rustc_version__0_2_3",
            path = rustc_version__0_2_3,
            build_file = "//third_party/rust/crates/remote:BUILD.rustc_version-0.2.3.bazel",
        )
    else:
        maybe(
            http_archive,
            name = "raze__rustc_version__0_2_3",
            url = "https://crates.io/api/v1/crates/rustc_version/0.2.3/download",
            type = "tar.gz",
            sha256 = "138e3e0acb6c9fb258b19b67cb8abd63c00679d2851805ea151465464fe9030a",
            strip_prefix = "rustc_version-0.2.3",
            build_file = Label("//third_party/rust/crates/remote:BUILD.rustc_version-0.2.3.bazel"),
        )

    if ryu__1_0_11:
        maybe(
            native.new_local_repository,
            name = "raze__ryu__1_0_11",
            path = ryu__1_0_11,
            build_file = "//third_party/rust/crates/remote:BUILD.ryu-1.0.11.bazel",
        )
    else:
        maybe(
            http_archive,
            name = "raze__ryu__1_0_11",
            url = "https://crates.io/api/v1/crates/ryu/1.0.11/download",
            type = "tar.gz",
            sha256 = "4501abdff3ae82a1c1b477a17252eb69cee9e66eb915c1abaa4f44d873df9f09",
            strip_prefix = "ryu-1.0.11",
            build_file = Label("//third_party/rust/crates/remote:BUILD.ryu-1.0.11.bazel"),
        )

    if semver__0_9_0:
        maybe(
            native.new_local_repository,
            name = "raze__semver__0_9_0",
            path = semver__0_9_0,
            build_file = "//third_party/rust/crates/remote:BUILD.semver-0.9.0.bazel",
        )
    else:
        maybe(
            http_archive,
            name = "raze__semver__0_9_0",
            url = "https://crates.io/api/v1/crates/semver/0.9.0/download",
            type = "tar.gz",
            sha256 = "1d7eb9ef2c18661902cc47e535f9bc51b78acd254da71d375c2f6720d9a40403",
            strip_prefix = "semver-0.9.0",
            build_file = Label("//third_party/rust/crates/remote:BUILD.semver-0.9.0.bazel"),
        )

    if semver_parser__0_7_0:
        maybe(
            native.new_local_repository,
            name = "raze__semver_parser__0_7_0",
            path = semver_parser__0_7_0,
            build_file = "//third_party/rust/crates/remote:BUILD.semver-parser-0.7.0.bazel",
        )
    else:
        maybe(
            http_archive,
            name = "raze__semver_parser__0_7_0",
            url = "https://crates.io/api/v1/crates/semver-parser/0.7.0/download",
            type = "tar.gz",
            sha256 = "388a1df253eca08550bef6c72392cfe7c30914bf41df5269b68cbd6ff8f570a3",
            strip_prefix = "semver-parser-0.7.0",
            build_file = Label("//third_party/rust/crates/remote:BUILD.semver-parser-0.7.0.bazel"),
        )

    if serde__1_0_144:
        maybe(
            native.new_local_repository,
            name = "raze__serde__1_0_144",
            path = serde__1_0_144,
            build_file = "//third_party/rust/crates/remote:BUILD.serde-1.0.144.bazel",
        )
    else:
        maybe(
            http_archive,
            name = "raze__serde__1_0_144",
            url = "https://crates.io/api/v1/crates/serde/1.0.144/download",
            type = "tar.gz",
            sha256 = "0f747710de3dcd43b88c9168773254e809d8ddbdf9653b84e2554ab219f17860",
            strip_prefix = "serde-1.0.144",
            build_file = Label("//third_party/rust/crates/remote:BUILD.serde-1.0.144.bazel"),
        )

    if serde_derive__1_0_144:
        maybe(
            native.new_local_repository,
            name = "raze__serde_derive__1_0_144",
            path = serde_derive__1_0_144,
            build_file = "//third_party/rust/crates/remote:BUILD.serde_derive-1.0.144.bazel",
        )
    else:
        maybe(
            http_archive,
            name = "raze__serde_derive__1_0_144",
            url = "https://crates.io/api/v1/crates/serde_derive/1.0.144/download",
            type = "tar.gz",
            sha256 = "94ed3a816fb1d101812f83e789f888322c34e291f894f19590dc310963e87a00",
            strip_prefix = "serde_derive-1.0.144",
            build_file = Label("//third_party/rust/crates/remote:BUILD.serde_derive-1.0.144.bazel"),
        )

    if serde_json__1_0_85:
        maybe(
            native.new_local_repository,
            name = "raze__serde_json__1_0_85",
            path = serde_json__1_0_85,
            build_file = "//third_party/rust/crates/remote:BUILD.serde_json-1.0.85.bazel",
        )
    else:
        maybe(
            http_archive,
            name = "raze__serde_json__1_0_85",
            url = "https://crates.io/api/v1/crates/serde_json/1.0.85/download",
            type = "tar.gz",
            sha256 = "e55a28e3aaef9d5ce0506d0a14dbba8054ddc7e499ef522dd8b26859ec9d4a44",
            strip_prefix = "serde_json-1.0.85",
            build_file = Label("//third_party/rust/crates/remote:BUILD.serde_json-1.0.85.bazel"),
        )

    if serialport__4_2_0:
        maybe(
            native.new_local_repository,
            name = "raze__serialport__4_2_0",
            path = serialport__4_2_0,
            build_file = "//third_party/rust/crates/remote:BUILD.serialport-4.2.0.bazel",
        )
    else:
        maybe(
            http_archive,
            name = "raze__serialport__4_2_0",
            url = "https://crates.io/api/v1/crates/serialport/4.2.0/download",
            type = "tar.gz",
            sha256 = "aab92efb5cf60ad310548bc3f16fa6b0d950019cb7ed8ff41968c3d03721cf12",
            strip_prefix = "serialport-4.2.0",
            build_file = Label("//third_party/rust/crates/remote:BUILD.serialport-4.2.0.bazel"),
        )

    if sha2__0_10_5:
        maybe(
            native.new_local_repository,
            name = "raze__sha2__0_10_5",
            path = sha2__0_10_5,
            build_file = "//third_party/rust/crates/remote:BUILD.sha2-0.10.5.bazel",
        )
    else:
        maybe(
            http_archive,
            name = "raze__sha2__0_10_5",
            url = "https://crates.io/api/v1/crates/sha2/0.10.5/download",
            type = "tar.gz",
            sha256 = "cf9db03534dff993187064c4e0c05a5708d2a9728ace9a8959b77bedf415dac5",
            strip_prefix = "sha2-0.10.5",
            build_file = Label("//third_party/rust/crates/remote:BUILD.sha2-0.10.5.bazel"),
        )

    if shellwords__1_1_0:
        maybe(
            native.new_local_repository,
            name = "raze__shellwords__1_1_0",
            path = shellwords__1_1_0,
            build_file = "//third_party/rust/crates/remote:BUILD.shellwords-1.1.0.bazel",
        )
    else:
        maybe(
            http_archive,
            name = "raze__shellwords__1_1_0",
            url = "https://crates.io/api/v1/crates/shellwords/1.1.0/download",
            type = "tar.gz",
            sha256 = "89e515aa4699a88148ed5ef96413ceef0048ce95b43fbc955a33bde0a70fcae6",
            strip_prefix = "shellwords-1.1.0",
            build_file = Label("//third_party/rust/crates/remote:BUILD.shellwords-1.1.0.bazel"),
        )

    if smallvec__1_9_0:
        maybe(
            native.new_local_repository,
            name = "raze__smallvec__1_9_0",
            path = smallvec__1_9_0,
            build_file = "//third_party/rust/crates/remote:BUILD.smallvec-1.9.0.bazel",
        )
    else:
        maybe(
            http_archive,
            name = "raze__smallvec__1_9_0",
            url = "https://crates.io/api/v1/crates/smallvec/1.9.0/download",
            type = "tar.gz",
            sha256 = "2fd0db749597d91ff862fd1d55ea87f7855a744a8425a64695b6fca237d1dad1",
            strip_prefix = "smallvec-1.9.0",
            build_file = Label("//third_party/rust/crates/remote:BUILD.smallvec-1.9.0.bazel"),
        )

    if spin__0_5_2:
        maybe(
            native.new_local_repository,
            name = "raze__spin__0_5_2",
            path = spin__0_5_2,
            build_file = "//third_party/rust/crates/remote:BUILD.spin-0.5.2.bazel",
        )
    else:
        maybe(
            http_archive,
            name = "raze__spin__0_5_2",
            url = "https://crates.io/api/v1/crates/spin/0.5.2/download",
            type = "tar.gz",
            sha256 = "6e63cff320ae2c57904679ba7cb63280a3dc4613885beafb148ee7bf9aa9042d",
            strip_prefix = "spin-0.5.2",
            build_file = Label("//third_party/rust/crates/remote:BUILD.spin-0.5.2.bazel"),
        )

    if spki__0_4_1:
        maybe(
            native.new_local_repository,
            name = "raze__spki__0_4_1",
            path = spki__0_4_1,
            build_file = "//third_party/rust/crates/remote:BUILD.spki-0.4.1.bazel",
        )
    else:
        maybe(
            http_archive,
            name = "raze__spki__0_4_1",
            url = "https://crates.io/api/v1/crates/spki/0.4.1/download",
            type = "tar.gz",
            sha256 = "5c01a0c15da1b0b0e1494112e7af814a678fec9bd157881b49beac661e9b6f32",
            strip_prefix = "spki-0.4.1",
            build_file = Label("//third_party/rust/crates/remote:BUILD.spki-0.4.1.bazel"),
        )

    if strsim__0_8_0:
        maybe(
            native.new_local_repository,
            name = "raze__strsim__0_8_0",
            path = strsim__0_8_0,
            build_file = "//third_party/rust/crates/remote:BUILD.strsim-0.8.0.bazel",
        )
    else:
        maybe(
            http_archive,
            name = "raze__strsim__0_8_0",
            url = "https://crates.io/api/v1/crates/strsim/0.8.0/download",
            type = "tar.gz",
            sha256 = "8ea5119cdb4c55b55d432abb513a0429384878c15dde60cc77b1c99de1a95a6a",
            strip_prefix = "strsim-0.8.0",
            build_file = Label("//third_party/rust/crates/remote:BUILD.strsim-0.8.0.bazel"),
        )

    if structopt__0_3_26:
        maybe(
            native.new_local_repository,
            name = "raze__structopt__0_3_26",
            path = structopt__0_3_26,
            build_file = "//third_party/rust/crates/remote:BUILD.structopt-0.3.26.bazel",
        )
    else:
        maybe(
            http_archive,
            name = "raze__structopt__0_3_26",
            url = "https://crates.io/api/v1/crates/structopt/0.3.26/download",
            type = "tar.gz",
            sha256 = "0c6b5c64445ba8094a6ab0c3cd2ad323e07171012d9c98b0b15651daf1787a10",
            strip_prefix = "structopt-0.3.26",
            build_file = Label("//third_party/rust/crates/remote:BUILD.structopt-0.3.26.bazel"),
        )

    if structopt_derive__0_4_18:
        maybe(
            native.new_local_repository,
            name = "raze__structopt_derive__0_4_18",
            path = structopt_derive__0_4_18,
            build_file = "//third_party/rust/crates/remote:BUILD.structopt-derive-0.4.18.bazel",
        )
    else:
        maybe(
            http_archive,
            name = "raze__structopt_derive__0_4_18",
            url = "https://crates.io/api/v1/crates/structopt-derive/0.4.18/download",
            type = "tar.gz",
            sha256 = "dcb5ae327f9cc13b68763b5749770cb9e048a99bd9dfdfa58d0cf05d5f64afe0",
            strip_prefix = "structopt-derive-0.4.18",
            build_file = Label("//third_party/rust/crates/remote:BUILD.structopt-derive-0.4.18.bazel"),
        )

    if subtle__2_4_1:
        maybe(
            native.new_local_repository,
            name = "raze__subtle__2_4_1",
            path = subtle__2_4_1,
            build_file = "//third_party/rust/crates/remote:BUILD.subtle-2.4.1.bazel",
        )
    else:
        maybe(
            http_archive,
            name = "raze__subtle__2_4_1",
            url = "https://crates.io/api/v1/crates/subtle/2.4.1/download",
            type = "tar.gz",
            sha256 = "6bdef32e8150c2a081110b42772ffe7d7c9032b606bc226c8260fd97e0976601",
            strip_prefix = "subtle-2.4.1",
            build_file = Label("//third_party/rust/crates/remote:BUILD.subtle-2.4.1.bazel"),
        )

    if syn__0_15_44:
        maybe(
            native.new_local_repository,
            name = "raze__syn__0_15_44",
            path = syn__0_15_44,
            build_file = "//third_party/rust/crates/remote:BUILD.syn-0.15.44.bazel",
        )
    else:
        maybe(
            http_archive,
            name = "raze__syn__0_15_44",
            url = "https://crates.io/api/v1/crates/syn/0.15.44/download",
            type = "tar.gz",
            sha256 = "9ca4b3b69a77cbe1ffc9e198781b7acb0c7365a883670e8f1c1bc66fba79a5c5",
            strip_prefix = "syn-0.15.44",
            build_file = Label("//third_party/rust/crates/remote:BUILD.syn-0.15.44.bazel"),
        )

    if syn__1_0_99:
        maybe(
            native.new_local_repository,
            name = "raze__syn__1_0_99",
            path = syn__1_0_99,
            build_file = "//third_party/rust/crates/remote:BUILD.syn-1.0.99.bazel",
        )
    else:
        maybe(
            http_archive,
            name = "raze__syn__1_0_99",
            url = "https://crates.io/api/v1/crates/syn/1.0.99/download",
            type = "tar.gz",
            sha256 = "58dbef6ec655055e20b86b15a8cc6d439cca19b667537ac6a1369572d151ab13",
            strip_prefix = "syn-1.0.99",
            build_file = Label("//third_party/rust/crates/remote:BUILD.syn-1.0.99.bazel"),
        )

    if synstructure__0_12_6:
        maybe(
            native.new_local_repository,
            name = "raze__synstructure__0_12_6",
            path = synstructure__0_12_6,
            build_file = "//third_party/rust/crates/remote:BUILD.synstructure-0.12.6.bazel",
        )
    else:
        maybe(
            http_archive,
            name = "raze__synstructure__0_12_6",
            url = "https://crates.io/api/v1/crates/synstructure/0.12.6/download",
            type = "tar.gz",
            sha256 = "f36bdaa60a83aca3921b5259d5400cbf5e90fc51931376a9bd4a0eb79aa7210f",
            strip_prefix = "synstructure-0.12.6",
            build_file = Label("//third_party/rust/crates/remote:BUILD.synstructure-0.12.6.bazel"),
        )

    if tempfile__3_3_0:
        maybe(
            native.new_local_repository,
            name = "raze__tempfile__3_3_0",
            path = tempfile__3_3_0,
            build_file = "//third_party/rust/crates/remote:BUILD.tempfile-3.3.0.bazel",
        )
    else:
        maybe(
            http_archive,
            name = "raze__tempfile__3_3_0",
            url = "https://crates.io/api/v1/crates/tempfile/3.3.0/download",
            type = "tar.gz",
            sha256 = "5cdb1ef4eaeeaddc8fbd371e5017057064af0911902ef36b39801f67cc6d79e4",
            strip_prefix = "tempfile-3.3.0",
            build_file = Label("//third_party/rust/crates/remote:BUILD.tempfile-3.3.0.bazel"),
        )

    if termcolor__1_1_3:
        maybe(
            native.new_local_repository,
            name = "raze__termcolor__1_1_3",
            path = termcolor__1_1_3,
            build_file = "//third_party/rust/crates/remote:BUILD.termcolor-1.1.3.bazel",
        )
    else:
        maybe(
            http_archive,
            name = "raze__termcolor__1_1_3",
            url = "https://crates.io/api/v1/crates/termcolor/1.1.3/download",
            type = "tar.gz",
            sha256 = "bab24d30b911b2376f3a13cc2cd443142f0c81dda04c118693e35b3835757755",
            strip_prefix = "termcolor-1.1.3",
            build_file = Label("//third_party/rust/crates/remote:BUILD.termcolor-1.1.3.bazel"),
        )

    if terminal_size__0_1_17:
        maybe(
            native.new_local_repository,
            name = "raze__terminal_size__0_1_17",
            path = terminal_size__0_1_17,
            build_file = "//third_party/rust/crates/remote:BUILD.terminal_size-0.1.17.bazel",
        )
    else:
        maybe(
            http_archive,
            name = "raze__terminal_size__0_1_17",
            url = "https://crates.io/api/v1/crates/terminal_size/0.1.17/download",
            type = "tar.gz",
            sha256 = "633c1a546cee861a1a6d0dc69ebeca693bf4296661ba7852b9d21d159e0506df",
            strip_prefix = "terminal_size-0.1.17",
            build_file = Label("//third_party/rust/crates/remote:BUILD.terminal_size-0.1.17.bazel"),
        )

    if textwrap__0_11_0:
        maybe(
            native.new_local_repository,
            name = "raze__textwrap__0_11_0",
            path = textwrap__0_11_0,
            build_file = "//third_party/rust/crates/remote:BUILD.textwrap-0.11.0.bazel",
        )
    else:
        maybe(
            http_archive,
            name = "raze__textwrap__0_11_0",
            url = "https://crates.io/api/v1/crates/textwrap/0.11.0/download",
            type = "tar.gz",
            sha256 = "d326610f408c7a4eb6f51c37c330e496b08506c9457c9d34287ecc38809fb060",
            strip_prefix = "textwrap-0.11.0",
            build_file = Label("//third_party/rust/crates/remote:BUILD.textwrap-0.11.0.bazel"),
        )

    if thiserror__1_0_34:
        maybe(
            native.new_local_repository,
            name = "raze__thiserror__1_0_34",
            path = thiserror__1_0_34,
            build_file = "//third_party/rust/crates/remote:BUILD.thiserror-1.0.34.bazel",
        )
    else:
        maybe(
            http_archive,
            name = "raze__thiserror__1_0_34",
            url = "https://crates.io/api/v1/crates/thiserror/1.0.34/download",
            type = "tar.gz",
            sha256 = "8c1b05ca9d106ba7d2e31a9dab4a64e7be2cce415321966ea3132c49a656e252",
            strip_prefix = "thiserror-1.0.34",
            build_file = Label("//third_party/rust/crates/remote:BUILD.thiserror-1.0.34.bazel"),
        )

    if thiserror_impl__1_0_34:
        maybe(
            native.new_local_repository,
            name = "raze__thiserror_impl__1_0_34",
            path = thiserror_impl__1_0_34,
            build_file = "//third_party/rust/crates/remote:BUILD.thiserror-impl-1.0.34.bazel",
        )
    else:
        maybe(
            http_archive,
            name = "raze__thiserror_impl__1_0_34",
            url = "https://crates.io/api/v1/crates/thiserror-impl/1.0.34/download",
            type = "tar.gz",
            sha256 = "e8f2591983642de85c921015f3f070c665a197ed69e417af436115e3a1407487",
            strip_prefix = "thiserror-impl-1.0.34",
            build_file = Label("//third_party/rust/crates/remote:BUILD.thiserror-impl-1.0.34.bazel"),
        )

    if time__0_1_44:
        maybe(
            native.new_local_repository,
            name = "raze__time__0_1_44",
            path = time__0_1_44,
            build_file = "//third_party/rust/crates/remote:BUILD.time-0.1.44.bazel",
        )
    else:
        maybe(
            http_archive,
            name = "raze__time__0_1_44",
            url = "https://crates.io/api/v1/crates/time/0.1.44/download",
            type = "tar.gz",
            sha256 = "6db9e6914ab8b1ae1c260a4ae7a49b6c5611b40328a735b21862567685e73255",
            strip_prefix = "time-0.1.44",
            build_file = Label("//third_party/rust/crates/remote:BUILD.time-0.1.44.bazel"),
        )

    if toml__0_5_9:
        maybe(
            native.new_local_repository,
            name = "raze__toml__0_5_9",
            path = toml__0_5_9,
            build_file = "//third_party/rust/crates/remote:BUILD.toml-0.5.9.bazel",
        )
    else:
        maybe(
            http_archive,
            name = "raze__toml__0_5_9",
            url = "https://crates.io/api/v1/crates/toml/0.5.9/download",
            type = "tar.gz",
            sha256 = "8d82e1a7758622a465f8cee077614c73484dac5b836c02ff6a40d5d1010324d7",
            strip_prefix = "toml-0.5.9",
            build_file = Label("//third_party/rust/crates/remote:BUILD.toml-0.5.9.bazel"),
        )

    if typenum__1_15_0:
        maybe(
            native.new_local_repository,
            name = "raze__typenum__1_15_0",
            path = typenum__1_15_0,
            build_file = "//third_party/rust/crates/remote:BUILD.typenum-1.15.0.bazel",
        )
    else:
        maybe(
            http_archive,
            name = "raze__typenum__1_15_0",
            url = "https://crates.io/api/v1/crates/typenum/1.15.0/download",
            type = "tar.gz",
            sha256 = "dcf81ac59edc17cc8697ff311e8f5ef2d99fcbd9817b34cec66f90b6c3dfd987",
            strip_prefix = "typenum-1.15.0",
            build_file = Label("//third_party/rust/crates/remote:BUILD.typenum-1.15.0.bazel"),
        )

    if typetag__0_1_8:
        maybe(
            native.new_local_repository,
            name = "raze__typetag__0_1_8",
            path = typetag__0_1_8,
            build_file = "//third_party/rust/crates/remote:BUILD.typetag-0.1.8.bazel",
        )
    else:
        maybe(
            http_archive,
            name = "raze__typetag__0_1_8",
            url = "https://crates.io/api/v1/crates/typetag/0.1.8/download",
            type = "tar.gz",
            sha256 = "4080564c5b2241b5bff53ab610082234e0c57b0417f4bd10596f183001505b8a",
            strip_prefix = "typetag-0.1.8",
            build_file = Label("//third_party/rust/crates/remote:BUILD.typetag-0.1.8.bazel"),
        )

    if typetag_impl__0_1_8:
        maybe(
            native.new_local_repository,
            name = "raze__typetag_impl__0_1_8",
            path = typetag_impl__0_1_8,
            build_file = "//third_party/rust/crates/remote:BUILD.typetag-impl-0.1.8.bazel",
        )
    else:
        maybe(
            http_archive,
            name = "raze__typetag_impl__0_1_8",
            url = "https://crates.io/api/v1/crates/typetag-impl/0.1.8/download",
            type = "tar.gz",
            sha256 = "e60147782cc30833c05fba3bab1d9b5771b2685a2557672ac96fa5d154099c0e",
            strip_prefix = "typetag-impl-0.1.8",
            build_file = Label("//third_party/rust/crates/remote:BUILD.typetag-impl-0.1.8.bazel"),
        )

    if unicode_ident__1_0_3:
        maybe(
            native.new_local_repository,
            name = "raze__unicode_ident__1_0_3",
            path = unicode_ident__1_0_3,
            build_file = "//third_party/rust/crates/remote:BUILD.unicode-ident-1.0.3.bazel",
        )
    else:
        maybe(
            http_archive,
            name = "raze__unicode_ident__1_0_3",
            url = "https://crates.io/api/v1/crates/unicode-ident/1.0.3/download",
            type = "tar.gz",
            sha256 = "c4f5b37a154999a8f3f98cc23a628d850e154479cd94decf3414696e12e31aaf",
            strip_prefix = "unicode-ident-1.0.3",
            build_file = Label("//third_party/rust/crates/remote:BUILD.unicode-ident-1.0.3.bazel"),
        )

    if unicode_segmentation__1_9_0:
        maybe(
            native.new_local_repository,
            name = "raze__unicode_segmentation__1_9_0",
            path = unicode_segmentation__1_9_0,
            build_file = "//third_party/rust/crates/remote:BUILD.unicode-segmentation-1.9.0.bazel",
        )
    else:
        maybe(
            http_archive,
            name = "raze__unicode_segmentation__1_9_0",
            url = "https://crates.io/api/v1/crates/unicode-segmentation/1.9.0/download",
            type = "tar.gz",
            sha256 = "7e8820f5d777f6224dc4be3632222971ac30164d4a258d595640799554ebfd99",
            strip_prefix = "unicode-segmentation-1.9.0",
            build_file = Label("//third_party/rust/crates/remote:BUILD.unicode-segmentation-1.9.0.bazel"),
        )

    if unicode_width__0_1_9:
        maybe(
            native.new_local_repository,
            name = "raze__unicode_width__0_1_9",
            path = unicode_width__0_1_9,
            build_file = "//third_party/rust/crates/remote:BUILD.unicode-width-0.1.9.bazel",
        )
    else:
        maybe(
            http_archive,
            name = "raze__unicode_width__0_1_9",
            url = "https://crates.io/api/v1/crates/unicode-width/0.1.9/download",
            type = "tar.gz",
            sha256 = "3ed742d4ea2bd1176e236172c8429aaf54486e7ac098db29ffe6529e0ce50973",
            strip_prefix = "unicode-width-0.1.9",
            build_file = Label("//third_party/rust/crates/remote:BUILD.unicode-width-0.1.9.bazel"),
        )

    if unicode_xid__0_1_0:
        maybe(
            native.new_local_repository,
            name = "raze__unicode_xid__0_1_0",
            path = unicode_xid__0_1_0,
            build_file = "//third_party/rust/crates/remote:BUILD.unicode-xid-0.1.0.bazel",
        )
    else:
        maybe(
            http_archive,
            name = "raze__unicode_xid__0_1_0",
            url = "https://crates.io/api/v1/crates/unicode-xid/0.1.0/download",
            type = "tar.gz",
            sha256 = "fc72304796d0818e357ead4e000d19c9c174ab23dc11093ac919054d20a6a7fc",
            strip_prefix = "unicode-xid-0.1.0",
            build_file = Label("//third_party/rust/crates/remote:BUILD.unicode-xid-0.1.0.bazel"),
        )

    if unicode_xid__0_2_3:
        maybe(
            native.new_local_repository,
            name = "raze__unicode_xid__0_2_3",
            path = unicode_xid__0_2_3,
            build_file = "//third_party/rust/crates/remote:BUILD.unicode-xid-0.2.3.bazel",
        )
    else:
        maybe(
            http_archive,
            name = "raze__unicode_xid__0_2_3",
            url = "https://crates.io/api/v1/crates/unicode-xid/0.2.3/download",
            type = "tar.gz",
            sha256 = "957e51f3646910546462e67d5f7599b9e4fb8acdd304b087a6494730f9eebf04",
            strip_prefix = "unicode-xid-0.2.3",
            build_file = Label("//third_party/rust/crates/remote:BUILD.unicode-xid-0.2.3.bazel"),
        )

    if vcpkg__0_2_15:
        maybe(
            native.new_local_repository,
            name = "raze__vcpkg__0_2_15",
            path = vcpkg__0_2_15,
            build_file = "//third_party/rust/crates/remote:BUILD.vcpkg-0.2.15.bazel",
        )
    else:
        maybe(
            http_archive,
            name = "raze__vcpkg__0_2_15",
            url = "https://crates.io/api/v1/crates/vcpkg/0.2.15/download",
            type = "tar.gz",
            sha256 = "accd4ea62f7bb7a82fe23066fb0957d48ef677f6eeb8215f372f52e48bb32426",
            strip_prefix = "vcpkg-0.2.15",
            build_file = Label("//third_party/rust/crates/remote:BUILD.vcpkg-0.2.15.bazel"),
        )

    if vec_map__0_8_2:
        maybe(
            native.new_local_repository,
            name = "raze__vec_map__0_8_2",
            path = vec_map__0_8_2,
            build_file = "//third_party/rust/crates/remote:BUILD.vec_map-0.8.2.bazel",
        )
    else:
        maybe(
            http_archive,
            name = "raze__vec_map__0_8_2",
            url = "https://crates.io/api/v1/crates/vec_map/0.8.2/download",
            type = "tar.gz",
            sha256 = "f1bddf1187be692e79c5ffeab891132dfb0f236ed36a43c7ed39f1165ee20191",
            strip_prefix = "vec_map-0.8.2",
            build_file = Label("//third_party/rust/crates/remote:BUILD.vec_map-0.8.2.bazel"),
        )

    if version_check__0_9_4:
        maybe(
            native.new_local_repository,
            name = "raze__version_check__0_9_4",
            path = version_check__0_9_4,
            build_file = "//third_party/rust/crates/remote:BUILD.version_check-0.9.4.bazel",
        )
    else:
        maybe(
            http_archive,
            name = "raze__version_check__0_9_4",
            url = "https://crates.io/api/v1/crates/version_check/0.9.4/download",
            type = "tar.gz",
            sha256 = "49874b5167b65d7193b8aba1567f5c7d93d001cafc34600cee003eda787e483f",
            strip_prefix = "version_check-0.9.4",
            build_file = Label("//third_party/rust/crates/remote:BUILD.version_check-0.9.4.bazel"),
        )

    if void__1_0_2:
        maybe(
            native.new_local_repository,
            name = "raze__void__1_0_2",
            path = void__1_0_2,
            build_file = "//third_party/rust/crates/remote:BUILD.void-1.0.2.bazel",
        )
    else:
        maybe(
            http_archive,
            name = "raze__void__1_0_2",
            url = "https://crates.io/api/v1/crates/void/1.0.2/download",
            type = "tar.gz",
            sha256 = "6a02e4885ed3bc0f2de90ea6dd45ebcbb66dacffe03547fadbb0eeae2770887d",
            strip_prefix = "void-1.0.2",
            build_file = Label("//third_party/rust/crates/remote:BUILD.void-1.0.2.bazel"),
        )

    if wasi__0_10_0_wasi_snapshot_preview1:
        maybe(
            native.new_local_repository,
            name = "raze__wasi__0_10_0_wasi_snapshot_preview1",
            path = wasi__0_10_0_wasi_snapshot_preview1,
            build_file = "//third_party/rust/crates/remote:BUILD.wasi-0.10.0+wasi-snapshot-preview1.bazel",
        )
    else:
        maybe(
            http_archive,
            name = "raze__wasi__0_10_0_wasi_snapshot_preview1",
            url = "https://crates.io/api/v1/crates/wasi/0.10.0+wasi-snapshot-preview1/download",
            type = "tar.gz",
            sha256 = "1a143597ca7c7793eff794def352d41792a93c481eb1042423ff7ff72ba2c31f",
            strip_prefix = "wasi-0.10.0+wasi-snapshot-preview1",
            build_file = Label("//third_party/rust/crates/remote:BUILD.wasi-0.10.0+wasi-snapshot-preview1.bazel"),
        )

    if wasi__0_11_0_wasi_snapshot_preview1:
        maybe(
            native.new_local_repository,
            name = "raze__wasi__0_11_0_wasi_snapshot_preview1",
            path = wasi__0_11_0_wasi_snapshot_preview1,
            build_file = "//third_party/rust/crates/remote:BUILD.wasi-0.11.0+wasi-snapshot-preview1.bazel",
        )
    else:
        maybe(
            http_archive,
            name = "raze__wasi__0_11_0_wasi_snapshot_preview1",
            url = "https://crates.io/api/v1/crates/wasi/0.11.0+wasi-snapshot-preview1/download",
            type = "tar.gz",
            sha256 = "9c8d87e72b64a3b4db28d11ce29237c246188f4f51057d65a7eab63b7987e423",
            strip_prefix = "wasi-0.11.0+wasi-snapshot-preview1",
            build_file = Label("//third_party/rust/crates/remote:BUILD.wasi-0.11.0+wasi-snapshot-preview1.bazel"),
        )

    if wasm_bindgen__0_2_83:
        maybe(
            native.new_local_repository,
            name = "raze__wasm_bindgen__0_2_83",
            path = wasm_bindgen__0_2_83,
            build_file = "//third_party/rust/crates/remote:BUILD.wasm-bindgen-0.2.83.bazel",
        )
    else:
        maybe(
            http_archive,
            name = "raze__wasm_bindgen__0_2_83",
            url = "https://crates.io/api/v1/crates/wasm-bindgen/0.2.83/download",
            type = "tar.gz",
            sha256 = "eaf9f5aceeec8be17c128b2e93e031fb8a4d469bb9c4ae2d7dc1888b26887268",
            strip_prefix = "wasm-bindgen-0.2.83",
            build_file = Label("//third_party/rust/crates/remote:BUILD.wasm-bindgen-0.2.83.bazel"),
        )

    if wasm_bindgen_backend__0_2_83:
        maybe(
            native.new_local_repository,
            name = "raze__wasm_bindgen_backend__0_2_83",
            path = wasm_bindgen_backend__0_2_83,
            build_file = "//third_party/rust/crates/remote:BUILD.wasm-bindgen-backend-0.2.83.bazel",
        )
    else:
        maybe(
            http_archive,
            name = "raze__wasm_bindgen_backend__0_2_83",
            url = "https://crates.io/api/v1/crates/wasm-bindgen-backend/0.2.83/download",
            type = "tar.gz",
            sha256 = "4c8ffb332579b0557b52d268b91feab8df3615f265d5270fec2a8c95b17c1142",
            strip_prefix = "wasm-bindgen-backend-0.2.83",
            build_file = Label("//third_party/rust/crates/remote:BUILD.wasm-bindgen-backend-0.2.83.bazel"),
        )

    if wasm_bindgen_macro__0_2_83:
        maybe(
            native.new_local_repository,
            name = "raze__wasm_bindgen_macro__0_2_83",
            path = wasm_bindgen_macro__0_2_83,
            build_file = "//third_party/rust/crates/remote:BUILD.wasm-bindgen-macro-0.2.83.bazel",
        )
    else:
        maybe(
            http_archive,
            name = "raze__wasm_bindgen_macro__0_2_83",
            url = "https://crates.io/api/v1/crates/wasm-bindgen-macro/0.2.83/download",
            type = "tar.gz",
            sha256 = "052be0f94026e6cbc75cdefc9bae13fd6052cdcaf532fa6c45e7ae33a1e6c810",
            strip_prefix = "wasm-bindgen-macro-0.2.83",
            build_file = Label("//third_party/rust/crates/remote:BUILD.wasm-bindgen-macro-0.2.83.bazel"),
        )

    if wasm_bindgen_macro_support__0_2_83:
        maybe(
            native.new_local_repository,
            name = "raze__wasm_bindgen_macro_support__0_2_83",
            path = wasm_bindgen_macro_support__0_2_83,
            build_file = "//third_party/rust/crates/remote:BUILD.wasm-bindgen-macro-support-0.2.83.bazel",
        )
    else:
        maybe(
            http_archive,
            name = "raze__wasm_bindgen_macro_support__0_2_83",
            url = "https://crates.io/api/v1/crates/wasm-bindgen-macro-support/0.2.83/download",
            type = "tar.gz",
            sha256 = "07bc0c051dc5f23e307b13285f9d75df86bfdf816c5721e573dec1f9b8aa193c",
            strip_prefix = "wasm-bindgen-macro-support-0.2.83",
            build_file = Label("//third_party/rust/crates/remote:BUILD.wasm-bindgen-macro-support-0.2.83.bazel"),
        )

    if wasm_bindgen_shared__0_2_83:
        maybe(
            native.new_local_repository,
            name = "raze__wasm_bindgen_shared__0_2_83",
            path = wasm_bindgen_shared__0_2_83,
            build_file = "//third_party/rust/crates/remote:BUILD.wasm-bindgen-shared-0.2.83.bazel",
        )
    else:
        maybe(
            http_archive,
            name = "raze__wasm_bindgen_shared__0_2_83",
            url = "https://crates.io/api/v1/crates/wasm-bindgen-shared/0.2.83/download",
            type = "tar.gz",
            sha256 = "1c38c045535d93ec4f0b4defec448e4291638ee608530863b1e2ba115d4fff7f",
            strip_prefix = "wasm-bindgen-shared-0.2.83",
            build_file = Label("//third_party/rust/crates/remote:BUILD.wasm-bindgen-shared-0.2.83.bazel"),
        )

    if winapi__0_3_9:
        maybe(
            native.new_local_repository,
            name = "raze__winapi__0_3_9",
            path = winapi__0_3_9,
            build_file = "//third_party/rust/crates/remote:BUILD.winapi-0.3.9.bazel",
        )
    else:
        maybe(
            http_archive,
            name = "raze__winapi__0_3_9",
            url = "https://crates.io/api/v1/crates/winapi/0.3.9/download",
            type = "tar.gz",
            sha256 = "5c839a674fcd7a98952e593242ea400abe93992746761e38641405d28b00f419",
            strip_prefix = "winapi-0.3.9",
            build_file = Label("//third_party/rust/crates/remote:BUILD.winapi-0.3.9.bazel"),
        )

    if winapi_i686_pc_windows_gnu__0_4_0:
        maybe(
            native.new_local_repository,
            name = "raze__winapi_i686_pc_windows_gnu__0_4_0",
            path = winapi_i686_pc_windows_gnu__0_4_0,
            build_file = "//third_party/rust/crates/remote:BUILD.winapi-i686-pc-windows-gnu-0.4.0.bazel",
        )
    else:
        maybe(
            http_archive,
            name = "raze__winapi_i686_pc_windows_gnu__0_4_0",
            url = "https://crates.io/api/v1/crates/winapi-i686-pc-windows-gnu/0.4.0/download",
            type = "tar.gz",
            sha256 = "ac3b87c63620426dd9b991e5ce0329eff545bccbbb34f3be09ff6fb6ab51b7b6",
            strip_prefix = "winapi-i686-pc-windows-gnu-0.4.0",
            build_file = Label("//third_party/rust/crates/remote:BUILD.winapi-i686-pc-windows-gnu-0.4.0.bazel"),
        )

    if winapi_util__0_1_5:
        maybe(
            native.new_local_repository,
            name = "raze__winapi_util__0_1_5",
            path = winapi_util__0_1_5,
            build_file = "//third_party/rust/crates/remote:BUILD.winapi-util-0.1.5.bazel",
        )
    else:
        maybe(
            http_archive,
            name = "raze__winapi_util__0_1_5",
            url = "https://crates.io/api/v1/crates/winapi-util/0.1.5/download",
            type = "tar.gz",
            sha256 = "70ec6ce85bb158151cae5e5c87f95a8e97d2c0c4b001223f33a334e3ce5de178",
            strip_prefix = "winapi-util-0.1.5",
            build_file = Label("//third_party/rust/crates/remote:BUILD.winapi-util-0.1.5.bazel"),
        )

    if winapi_x86_64_pc_windows_gnu__0_4_0:
        maybe(
            native.new_local_repository,
            name = "raze__winapi_x86_64_pc_windows_gnu__0_4_0",
            path = winapi_x86_64_pc_windows_gnu__0_4_0,
            build_file = "//third_party/rust/crates/remote:BUILD.winapi-x86_64-pc-windows-gnu-0.4.0.bazel",
        )
    else:
        maybe(
            http_archive,
            name = "raze__winapi_x86_64_pc_windows_gnu__0_4_0",
            url = "https://crates.io/api/v1/crates/winapi-x86_64-pc-windows-gnu/0.4.0/download",
            type = "tar.gz",
            sha256 = "712e227841d057c1ee1cd2fb22fa7e5a5461ae8e48fa2ca79ec42cfc1931183f",
            strip_prefix = "winapi-x86_64-pc-windows-gnu-0.4.0",
            build_file = Label("//third_party/rust/crates/remote:BUILD.winapi-x86_64-pc-windows-gnu-0.4.0.bazel"),
        )

    if zerocopy__0_5_0:
        maybe(
            native.new_local_repository,
            name = "raze__zerocopy__0_5_0",
            path = zerocopy__0_5_0,
            build_file = "//third_party/rust/crates/remote:BUILD.zerocopy-0.5.0.bazel",
        )
    else:
        maybe(
            http_archive,
            name = "raze__zerocopy__0_5_0",
            url = "https://crates.io/api/v1/crates/zerocopy/0.5.0/download",
            type = "tar.gz",
            sha256 = "5e59ec1d2457bd6c0dd89b50e7d9d6b0b647809bf3f0a59ac85557046950b7b2",
            strip_prefix = "zerocopy-0.5.0",
            build_file = Label("//third_party/rust/crates/remote:BUILD.zerocopy-0.5.0.bazel"),
        )

    if zerocopy_derive__0_3_1:
        maybe(
            native.new_local_repository,
            name = "raze__zerocopy_derive__0_3_1",
            path = zerocopy_derive__0_3_1,
            build_file = "//third_party/rust/crates/remote:BUILD.zerocopy-derive-0.3.1.bazel",
        )
    else:
        maybe(
            http_archive,
            name = "raze__zerocopy_derive__0_3_1",
            url = "https://crates.io/api/v1/crates/zerocopy-derive/0.3.1/download",
            type = "tar.gz",
            sha256 = "a0fbc82b82efe24da867ee52e015e58178684bd9dd64c34e66bdf21da2582a9f",
            strip_prefix = "zerocopy-derive-0.3.1",
            build_file = Label("//third_party/rust/crates/remote:BUILD.zerocopy-derive-0.3.1.bazel"),
        )

    if zeroize__1_4_3:
        maybe(
            native.new_local_repository,
            name = "raze__zeroize__1_4_3",
            path = zeroize__1_4_3,
            build_file = "//third_party/rust/crates/remote:BUILD.zeroize-1.4.3.bazel",
        )
    else:
        maybe(
            http_archive,
            name = "raze__zeroize__1_4_3",
            url = "https://crates.io/api/v1/crates/zeroize/1.4.3/download",
            type = "tar.gz",
            sha256 = "d68d9dcec5f9b43a30d38c49f91dfedfaac384cb8f085faca366c26207dd1619",
            strip_prefix = "zeroize-1.4.3",
            build_file = Label("//third_party/rust/crates/remote:BUILD.zeroize-1.4.3.bazel"),
        )

    if zeroize_derive__1_3_2:
        maybe(
            native.new_local_repository,
            name = "raze__zeroize_derive__1_3_2",
            path = zeroize_derive__1_3_2,
            build_file = "//third_party/rust/crates/remote:BUILD.zeroize_derive-1.3.2.bazel",
        )
    else:
        maybe(
            http_archive,
            name = "raze__zeroize_derive__1_3_2",
            url = "https://crates.io/api/v1/crates/zeroize_derive/1.3.2/download",
            type = "tar.gz",
            sha256 = "3f8f187641dad4f680d25c4bfc4225b418165984179f26ca76ec4fb6441d3a17",
            strip_prefix = "zeroize_derive-1.3.2",
            build_file = Label("//third_party/rust/crates/remote:BUILD.zeroize_derive-1.3.2.bazel"),
        )

