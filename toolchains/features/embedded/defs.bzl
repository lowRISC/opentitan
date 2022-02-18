load("//toolchains/features/embedded/impl:gcc.bzl", "GetGccEmbeddedFeatures")
load("//toolchains/features/embedded/impl:clang.bzl", "GetClangEmbeddedFeatures")

_IMPL_LOOKUP = {
    "GCC": GetGccEmbeddedFeatures,
    "CLANG": GetClangEmbeddedFeatures,
}

def GetEmbeddedFeatures(compiler, architecture, float_abi, endian, fpu):
    return _IMPL_LOOKUP[compiler](architecture, float_abi, endian, fpu)
