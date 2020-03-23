def _is_feature(var):
    result = False
    if var:
        if var.type_name == "feature":
            result = True
    return result

_CC_ALL_COMMON_FEATURES_INFO = {
    "exceptions": "Features for c++ exception configuration (Must disable C++ exceptions by default)",
    "runtime_type_information": "Features for enabling runtime type information (Must allow RTTI by default)",
    "sys_spec": "Configuration for the system spec (Must default to no system spec)",
    "cc_constructor_destructor": "Must disable destructors on global c++ variables, and allow instantiation of global variables only once",
    "type_name": "The type name for this provider",
}
CcAllEmbeddedFeatureInfo = provider(fields = _CC_ALL_COMMON_FEATURES_INFO)

def all_embedded_features(
        exceptions,
        runtime_type_information,
        sys_spec,
        cc_constructor_destructor):
    """ all_common_features represents the minimal set of features that should be implemented for a portable toolchain

    Args:
        exceptions: Enable/disable c++ exceptions (disable by default)
        runtime_type_information: Compile with run time type information (disable by default)
        sys_spec: Define the system spec for this target (Must default ot no system spec)
        cc_constructor_destructor: Must disable destructors on global c++ variables, and allow instantiation of global variables only once (Should be enabled by default)

    Returns:
        CCAllEmbeddedFeatureInfo: All the common embedded features required to make a minimal toolchain
    """
    args = [
        exceptions,
        runtime_type_information,
        sys_spec,
        cc_constructor_destructor,
    ]
    for arg in args:
        if not _is_feature(arg):
            fail("All arguments should be features", arg)
        if arg.name not in _CC_ALL_COMMON_FEATURES_INFO.keys():
            fail("All arguments should have a name corresponding to a provider field, got arg.name:", arg.name, ", which is not in required providers")

    return CcAllEmbeddedFeatureInfo(
        exceptions = exceptions,
        runtime_type_information = runtime_type_information,
        sys_spec = sys_spec,
        cc_constructor_destructor = cc_constructor_destructor,
    )
