load("//toolchains/features/embedded/impl:gcc.bzl", "GetGccEmbeddedFeatures")

_IMPL_LOOKUP = {
    "GCC": GetGccEmbeddedFeatures,
}

def GetEmbeddedFeatures(compiler, architecture, float_abi, endian, fpu):
    return _IMPL_LOOKUP[compiler](architecture, float_abi, endian, fpu)
