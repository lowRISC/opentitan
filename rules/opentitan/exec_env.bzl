# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("@bazel_skylib//lib:types.bzl", "types")
load("@lowrisc_opentitan//rules/opentitan:providers.bzl", "PROVIDER_FIELDS")
load("@lowrisc_opentitan//rules/opentitan:util.bzl", "get_fallback", "get_files")
load("//rules/opentitan:toolchain.bzl", "LOCALTOOLS_TOOLCHAIN")

# ExecEnvInfo provider fields and whether the field is required.
_FIELDS = {
    "design": ("attr.design", True),
    "exec_env": ("attr.exec_env", False),
    "lib": ("attr.lib", True),
    "linker_script": ("attr.linker_script", False),
    "rsa_key": ("attr.rsa_key", False),
    "spx_key": ("attr.spx_key", False),
    "manifest": ("file.manifest", False),
    "rom": ("attr.rom", False),
    "rom_mmi": ("file.rom_mmi", False),
    "rom_ext": ("attr.rom_ext", False),
    "otp": ("file.otp", False),
    "otp_mmi": ("file.otp_mmi", False),
    "base_bitstream": ("file.base_bitstream", False),
    "args": ("attr.args", False),
    "test_cmd": ("attr.test_cmd", False),
    "param": ("attr.param", False),
    "data": ("attr.data", False),
    "extract_sw_logs": ("attr.extract_sw_logs", False),
    "otp_mmap": ("file.otp_mmap", False),
    "otp_seed": ("attr.otp_seed", False),
    "otp_data_perm": ("attr.otp_data_perm", False),
    "flash_scramble_tool": ("attr.flash_scramble_tool", False),
    "rom_scramble_config": ("file.rom_scramble_config", False),
}

ExecEnvInfo = provider(
    doc = "Execution Environment Info",
)

_unbound = struct(unbound = True)

def getattr_path(obj, path, defval = _unbound):
    """Gets a named item from an object hierarchy.

    This function is like `getattr`, but it walks an object path instead of
    retrieving a single item.

    Args:
      obj: The root of an object hierarchy.
      path: An object path to the desired attribute (e.g. attr.srcs).
      defval: An optional default value if the item is not found.
    Returns:
      The requested object or defval.
    """
    path = path.split(".")
    item = path.pop(-1)
    for p in path:
        obj = getattr(obj, p, None)
    val = getattr(obj, item, defval)
    if val == _unbound:
        fail("Item '{}' not found in object".format(path))
    return val

def exec_env_as_dict(ctx):
    """Initialize provider fields, possibly inheriting from a base provider.

    This function will return a dict of ExecEnvInfo provider fields, preferring
    the values in the `ctx` object and falling back to the base provider (if given).

    Args:
      ctx: The rule context.
    Returns:
      dict: A dict of items to initialize in the ExecEnvInfo provider.
    """
    base = ctx.attr.base
    if base:
        base = base[ExecEnvInfo]
    tc = ctx.toolchains[LOCALTOOLS_TOOLCHAIN]
    result = {
        "_opentitantool": tc.tools.opentitantool,
    }
    for field, (path, required) in _FIELDS.items():
        val = getattr_path(ctx, path)
        if not val and base:
            # If the value doesn't exist in the context object, get the value
            # from the base provider (if present).
            val = getattr(base, field)

        if required and not val:
            fail("No value for required field {} in {}".format(field, ctx.attr.name))
        result[field] = val
    return result

def exec_env_common_attrs(**kwargs):
    """Common attributes for rules creating ExecEnvInfo providers."""
    return {
        "base": attr.label(
            default = kwargs.get("base"),
            providers = [ExecEnvInfo],
            doc = "Base execution environment used to initialize this environment",
        ),
        "design": attr.string(
            default = kwargs.get("design", ""),
            doc = "Top-level hardware design name (e.g. `earlgrey`)",
        ),
        "exec_env": attr.string(
            default = kwargs.get("exec_env", "{name}"),
            doc = "Name of the execution environment (e.g. `fpga_cw310`)",
        ),
        "lib": attr.label(
            default = kwargs.get("lib"),
            providers = [CcInfo],
            doc = "Library providing environment-specific constants",
        ),
        "linker_script": attr.label(
            default = kwargs.get("linker_script"),
            providers = [CcInfo],
            doc = "Library providing the environment-specific linker script",
        ),
        "rsa_key": attr.label_keyed_string_dict(
            default = kwargs.get("rsa_key", {}),
            allow_files = True,
            doc = "RSA key to sign images",
        ),
        "spx_key": attr.label_keyed_string_dict(
            default = kwargs.get("spx_key", {}),
            allow_files = True,
            doc = "SPX key to sign images",
        ),
        "manifest": attr.label(
            default = kwargs.get("manifest"),
            allow_single_file = True,
            doc = "Manifest used when signing images",
        ),
        "rom": attr.label(
            default = kwargs.get("rom"),
            allow_files = True,
            doc = "ROM image to use in this environment",
        ),
        "rom_mmi": attr.label(
            default = kwargs.get("rom_mmi"),
            allow_single_file = True,
            doc = "Memory layout description for ROM splicing",
        ),
        "rom_ext": attr.label(
            default = kwargs.get("rom_ext"),
            allow_files = True,
            doc = "ROM_EXT image to use in this environment",
        ),
        "otp": attr.label(
            default = kwargs.get("otp"),
            allow_single_file = True,
            doc = "OTP image to use in this environment",
        ),
        "otp_mmi": attr.label(
            default = kwargs.get("otp_mmi"),
            allow_single_file = True,
            doc = "Memory layout description for OTP splicing",
        ),
        "base_bitstream": attr.label(
            default = kwargs.get("base_bitstream"),
            allow_single_file = True,
            doc = "Bitstream to use in this environment",
        ),
        "args": attr.string_list(
            default = kwargs.get("args", []),
            doc = "Pre-test_cmd arguments in this environment",
        ),
        "test_cmd": attr.string(
            default = kwargs.get("test_cmd", ""),
            doc = "Command to execute a test in this environment",
        ),
        "param": attr.string_dict(
            default = kwargs.get("param", {}),
            doc = "Additional parameters for this environment or test",
        ),
        "data": attr.label_list(
            default = kwargs.get("data", []),
            allow_files = True,
            cfg = "exec",
            doc = "Additonal dependencies for this environment or test",
        ),
        "extract_sw_logs": attr.label(
            default = kwargs.get("extract_sw_logs"),
            executable = True,
            cfg = "exec",
        ),
        "otp_mmap": attr.label(
            allow_single_file = True,
            default = kwargs.get("otp_mmap"),
            doc = "OTP memory map configuration HJSON file.",
        ),
        "otp_seed": attr.label(
            default = kwargs.get("otp_seed"),
            doc = "Configuration override seed used to randomize OTP netlist constants.",
        ),
        "otp_data_perm": attr.label(
            default = kwargs.get("otp_data_perm"),
            doc = "Option to indicate OTP VMEM file bit layout.",
        ),
        "flash_scramble_tool": attr.label(
            default = kwargs.get("flash_scramble_tool"),
            executable = True,
            cfg = "exec",
        ),
        "rom_scramble_tool": attr.label(
            doc = "ROM scrambling tool.",
            default = "//hw/ip/rom_ctrl/util:scramble_image",
            executable = True,
            cfg = "exec",
        ),
        "rom_scramble_config": attr.label(
            default = kwargs.get("rom_scramble_config", None),
            doc = "ROM scrambling config for this environment",
            allow_single_file = True,
        ),
    }

def _do_update(name, file, data_files, param, action_param):
    """Update the files list and param dictionaries."""
    if name in param:
        fail(name, "already exists in the param dictionary")
    data_files.append(file)
    param[name] = file.short_path
    if action_param != None:
        action_param[name] = file.path

def _update(name, file, data_files, param, action_param):
    """Update the files list and param dictionaries."""
    if types.is_list(file) or types.is_tuple(file):
        for i, f in enumerate(file):
            _do_update("{}:{}".format(name, i), f, data_files, param, action_param)
    else:
        _do_update(name, file, data_files, param, action_param)

def update_file_provider(name, provider, data_files, param, action_param = None, default = "default"):
    """Map available provider files into a file list and param dictionary.

    All available Files will be added into the data_files list and param
    dictionary.  Dict keys will be named as `name:fieldname` for all
    non-default items in the provider.

    Args:
      name: The name of the item to add to the param dictionary.
      provider: The provider contaning the files.
      data_files: A list of files to append available files into.
      param: A mapping of item names to file short_paths.
      action_param: A mapping of item names to full file paths.
      default: The element of the provider to consider as the default item.
    Returns:
      None
    """
    if not provider:
        # Nothing to do.
        return
    for field in PROVIDER_FIELDS:
        file = getattr(provider, field, None)
        if not file:
            continue
        if field == default:
            _update(name, file, data_files, param, action_param)
        else:
            _update("{}:{}".format(name, field), file, data_files, param, action_param)

def update_file_attr(name, attr, provider, data_files, param, action_param = None, default = "default"):
    """Map available attr files into a file list and param dictionary.

    All available Files will be added into the data_files list and param
    dictionary.  Dict keys will be named as `name:fieldname` for all
    non-default items in the provider.

    If the `provider` is not present in `attr`, DefaultInfo will be inspected.

    Args:
      name: The name of the item to add to the param dictionary.
      attr: The attribute holding the files.
      provider: The provider to check in `attr`.
      data_files: A list of files to append available files into.
      param: A mapping of item names to file short_paths.
      action_param: A mapping of item names to full file paths.
      default: The element of the provider to consider as the default item.
    Returns:
      None
    """

    if not attr:
        # Nothing to do.
        return
    if types.is_list(attr):
        if len(attr) == 1:
            attr = attr[0]
        else:
            fail("attr must be a single item")
    if type(attr) == "File":
        _update(name, attr, data_files, param, action_param)
    elif provider and provider in attr:
        update_file_provider(name, attr[provider], data_files, param, action_param, default)
    elif DefaultInfo in attr:
        file = attr[DefaultInfo].files.to_list()
        if len(file) > 1:
            fail("Expected to find exactly one file in", attr)
        _update(name, file[0], data_files, param, action_param)
    else:
        fail("No file providers in", attr)

def common_test_setup(ctx, exec_env, firmware):
    """Perform the common test setup used by the exec_envs.

    Args:
      ctx: The rule context for this test.
      exec_env: The execution environment for this test.
      firmware: The firmware for this test.
    Returns:
      (test_harness, data_labels, data_files, param, action_param)
    """

    # If there is no explicitly specified test_harness, then the harness is opentitantool.
    if ctx.attr.test_harness:
        test_harness = ctx.attr.test_harness.files_to_run
    else:
        test_harness = exec_env._opentitantool

    # Get the files we'll need to run the test.
    data_labels = ctx.attr.data + exec_env.data
    data_files = get_files(data_labels)
    data_files.append(test_harness.executable)

    # Construct a param dictionary by combining the exec_env.param, the rule's
    # param and and some extra file references.
    param = dict(exec_env.param)
    param.update(ctx.attr.param)
    action_param = dict(param)

    # Collect all file resource specified in the exec_env or as overrides.
    update_file_attr("bitstream", ctx.attr.bitstream, None, data_files, param, action_param)

    otp = get_fallback(ctx, "attr.otp", exec_env)
    update_file_attr("otp", otp, None, data_files, param, action_param)

    if ctx.attr.kind == "rom" and firmware:
        # If its a "rom" test, then the firmware built by the rule should be
        # loaded into ROM.
        update_file_provider("rom", firmware, data_files, param, action_param)
    else:
        rom = get_fallback(ctx, "attr.rom", exec_env)
        update_file_attr("rom", rom, exec_env.provider, data_files, param, action_param, default = "rom")

    rom_ext = get_fallback(ctx, "attr.rom_ext", exec_env)
    update_file_attr("rom_ext", rom_ext, exec_env.provider, data_files, param, action_param)

    # Add the binaries built by the test or added to the test.
    update_file_provider("firmware", firmware, data_files, param, action_param)
    for attr, name in ctx.attr.binaries.items():
        update_file_attr(name, attr, exec_env.provider, data_files, param, action_param)

    return test_harness, data_labels, data_files, param, action_param
