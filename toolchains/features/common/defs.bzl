load("//toolchains/features/common/impl:gcc.bzl", "GetGccCommonFeatures")
load("//toolchains/features/common/impl:clang.bzl", "GetClangCommonFeatures")

_IMPL_LOOKUP = {
    "GCC": GetGccCommonFeatures,
    "CLANG": GetClangCommonFeatures,
}

def GetCommonFeatures(compiler, architecture, float_abi, endian, fpu, include_paths, sysroot):
    if compiler not in _IMPL_LOOKUP.keys():
        fail("This compiler is not currently supported, please use: ", ",".join(_IMPL_LOOKUP.keys()))
    return _IMPL_LOOKUP[compiler](include_paths, sysroot, architecture, float_abi, endian, fpu)
