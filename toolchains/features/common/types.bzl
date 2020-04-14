"""load(
    "@bazel_tools//tools/cpp:cc_toolchain_config_lib.bzl",
    "feature"
)"""

def _is_feature(var):
    result = False
    if var:
        if var.type_name == "feature":
            result = True
    return result

CC_ALL_COMMON_FEATURES_INFO = {
    "all_warnings": "Contains feature to enable all warnings",
    "all_warnings_as_errors": "Contains a feature to treat all warnings as errors",
    "reproducible": "Contains a feature to ensure reproducible builds, this feature should be enabled by default",
    "includes": "Contains a feature that includes all neccesary system headers",
    "symbol_garbage_collection": "Garbage collect section at link time",
    "architecture": "Features relevant to the target architecture",
    "dbg": "Compile with debug symbols",
    "opt": "Compile a release build with, optimisation turned on",
    "fastbuild": "Compile quickly, for fast development",
    "output_format": "The output format of the compilers *.stripped target, (default binary)",
    "type_name": "The type name for this provider",
}

CcAllCommonFeaturesInfo = provider(fields = CC_ALL_COMMON_FEATURES_INFO)

def all_common_features(
        all_warnings,
        all_warnings_as_errors,
        reproducible,
        includes,
        symbol_garbage_collection,
        architecture,
        dbg,
        opt,
        fastbuild,
        output_format):
    """ all_common_features represents the minimal set of features that should be implemented for a portable toolchain

    Args:
        all_warnings: Enable all warnings
        all_warnings_as_errors: Treat all warnings as errors
        reproducible: Make builds reproducible
        includes: Define all the include paths
        symbol_garbage_collection: Garbage collect sections at link time
        architecture: Define the architecture of your system
        dbg: Configure the debug compilation mode
        opt: Configure the optimal/release compilation mode
        fastbuild: Configure the fastbuild mode, to speed up developement
        output_format: The output format for the {target}.stripped target (default binary)

    Returns:
        CCAllCommonFeaturesInfo: All the common features required to make a minimal toolchain
    """
    args = [
        all_warnings,
        all_warnings_as_errors,
        reproducible,
        includes,
        symbol_garbage_collection,
        dbg,
        opt,
        fastbuild,
        output_format,
    ]
    for arg in args:
        if not _is_feature(arg):
            fail("All arguments should be features", arg)
        if arg.name not in CC_ALL_COMMON_FEATURES_INFO.keys():
            fail("All arguments should have a name corresponding to a provider field, got arg.name:", arg.name, ", which is not in required providers")

    return CcAllCommonFeaturesInfo(
        all_warnings = all_warnings,
        all_warnings_as_errors = all_warnings_as_errors,
        reproducible = reproducible,
        includes = includes,
        symbol_garbage_collection = symbol_garbage_collection,
        architecture = architecture,
        dbg = dbg,
        opt = opt,
        fastbuild = fastbuild,
        output_format = output_format,
        type_name = "cc_all_common_feature_info",
    )
