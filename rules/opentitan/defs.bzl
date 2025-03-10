# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

"""Rules to build OpenTitan for the RISC-V target"""

load("@bazel_skylib//lib:sets.bzl", "sets")
load(
    "@lowrisc_opentitan//rules:rv.bzl",
    _OPENTITAN_CPU = "OPENTITAN_CPU",
    _OPENTITAN_PLATFORM = "OPENTITAN_PLATFORM",
    _opentitan_transition = "opentitan_transition",
)
load(
    "@lowrisc_opentitan//rules/opentitan:cc.bzl",
    _opentitan_binary = "opentitan_binary",
    _opentitan_test = "opentitan_test",
)
load(
    "@lowrisc_opentitan//rules/opentitan:ci.bzl",
    "ci_orchestrator",
)
load(
    "@lowrisc_opentitan//rules/opentitan:fpga.bzl",
    _fpga_cw305 = "fpga_cw305",
    _fpga_cw310 = "fpga_cw310",
    _fpga_cw340 = "fpga_cw340",
    _fpga_params = "fpga_params",
)
load(
    "@lowrisc_opentitan//rules/opentitan:keyutils.bzl",
    _ecdsa_key_by_name = "ecdsa_key_by_name",
    _ecdsa_key_for_lc_state = "ecdsa_key_for_lc_state",
    _rsa_key_by_name = "rsa_key_by_name",
    _rsa_key_for_lc_state = "rsa_key_for_lc_state",
    _spx_key_by_name = "spx_key_by_name",
    _spx_key_for_lc_state = "spx_key_for_lc_state",
)
load(
    "@lowrisc_opentitan//rules/opentitan:manual.bzl",
    _opentitan_manual_test = "opentitan_manual_test",
)
load(
    "@lowrisc_opentitan//rules/opentitan:silicon.bzl",
    _silicon = "silicon",
    _silicon_params = "silicon_params",
)
load(
    "@lowrisc_opentitan//rules/opentitan:sim_dv.bzl",
    _dv_params = "dv_params",
    _sim_dv = "sim_dv",
)
load(
    "@lowrisc_opentitan//rules/opentitan:sim_verilator.bzl",
    _sim_verilator = "sim_verilator",
    _verilator_params = "verilator_params",
)
load(
    "@lowrisc_opentitan//rules/opentitan:qemu.bzl",
    _qemu_params = "qemu_params",
    _sim_qemu = "sim_qemu",
)
load(
    "@lowrisc_opentitan//hw/top:defs.bzl",
    "ALL_TOPS",
    "opentitan_select_top",
)

# The following definition is used to clear the key set in the signing
# configuration for execution environments (exec_env) and opentitan_test
# and opentitan_binary rules.
CLEAR_KEY_SET = {"//signing:none_key": "none_key"}

# Re-exports of names from transition.bzl
OPENTITAN_CPU = _OPENTITAN_CPU
OPENTITAN_PLATFORM = _OPENTITAN_PLATFORM
opentitan_transition = _opentitan_transition

fpga_cw305 = _fpga_cw305
fpga_cw310 = _fpga_cw310
fpga_cw340 = _fpga_cw340
fpga_params = _fpga_params

# Temporary export of the old name to prevent merge skew breakage.
cw310_params = _fpga_params

silicon = _silicon
silicon_params = _silicon_params

sim_verilator = _sim_verilator
verilator_params = _verilator_params

sim_dv = _sim_dv
dv_params = _dv_params

sim_qemu = _sim_qemu
qemu_params = _qemu_params

ecdsa_key_for_lc_state = _ecdsa_key_for_lc_state
ecdsa_key_by_name = _ecdsa_key_by_name

rsa_key_for_lc_state = _rsa_key_for_lc_state
rsa_key_by_name = _rsa_key_by_name

spx_key_for_lc_state = _spx_key_for_lc_state
spx_key_by_name = _spx_key_by_name

opentitan_manual_test = _opentitan_manual_test

# The default set of test environments for Earlgrey.
EARLGREY_TEST_ENVS = {
    "//hw/top_earlgrey:fpga_cw310_sival_rom_ext": None,
    "//hw/top_earlgrey:fpga_cw310_rom_with_fake_keys": None,
    "//hw/top_earlgrey:sim_dv": None,
    "//hw/top_earlgrey:sim_verilator": None,
    "//hw/top_earlgrey:sim_qemu_rom_with_fake_keys": None,
}

# The default set of test environments for Earlgrey.
EARLGREY_SILICON_OWNER_ROM_EXT_ENVS = {
    "//hw/top_earlgrey:silicon_owner_sival_rom_ext": None,
}

# All CW340 test environments for Earlgrey.
EARLGREY_CW340_TEST_ENVS = {
    "//hw/top_earlgrey:fpga_cw340_test_rom": None,
    "//hw/top_earlgrey:fpga_cw340_rom_with_fake_keys": None,
    "//hw/top_earlgrey:fpga_cw340_sival": None,
    "//hw/top_earlgrey:fpga_cw340_sival_rom_ext": None,
    "//hw/top_earlgrey:fpga_cw340_rom_ext": None,
}

# The default set of test environments for Darjeeling.
DARJEELING_TEST_ENVS = {
    "//hw/top_darjeeling:sim_dv": None,
}

# Messages we expect for possible test outcomes.
OTTF_SUCCESS_MSG = r"PASS.*\n"
OTTF_FAILURE_MSG = r"(FAIL|FAULT).*\n"
ROM_BOOT_FAILURE_MSG = "BFV:[0-9a-f]{8}"

# These are defined for positive test cases and should be flipped for negative
# test cases, i.e., when a test failure is the expected outcome.
DEFAULT_TEST_SUCCESS_MSG = OTTF_SUCCESS_MSG
DEFAULT_TEST_FAILURE_MSG = "({})|({})".format(
    OTTF_FAILURE_MSG,
    ROM_BOOT_FAILURE_MSG,
)

# Use to clear the default `test_cmd` from any execution environment.
CLEAR_TEST_CMD = " "

def _parameter_name(env, pname):
    if not pname:
        (_, suffix) = env.split(":")
        if "fpga" in suffix:
            pname = "fpga"
        elif "verilator" in suffix:
            pname = "verilator"
        elif "dv" in suffix:
            pname = "dv"
        elif "silicon" in suffix:
            pname = "silicon"
        elif "qemu" in suffix:
            pname = "qemu"
        else:
            fail("Unable to identify parameter block name:", env)
    return pname

def _hacky_tags(env):
    (_, suffix) = env.split(":")
    tags = []
    if suffix.startswith("fpga"):
        tags.append("fpga")

        # We have tags like "cw310_rom_with_real_keys" or "cw310_test_rom"
        # applied to our tests.  Since there is no way to adjust tags in a
        # rule's implementation, we have to infer these tag names from the
        # label name.
        subtag = suffix[5:]
        tags.append(subtag)

        # Also add the kind of FPGA by itself (e.g. "hyper310" or "cw340").
        fpga_kind = subtag.split("_")[0]
        tags.append(fpga_kind)
    if suffix.startswith("sim"):
        # Add the kind of simulator by itself (e.g. "verilator" or "qemu").
        sim_kind = suffix.split("_")[1]
        tags.append(sim_kind)
    if suffix.startswith("silicon") or suffix.startswith("sim"):
        # We add the entire suffix for silicon and sim exec environments
        # to be able to filter tests by them. "silicon_creator" and
        # "silicon_owner_sival_rom_ext" have different target configurations.
        tags.append(suffix)
    return tags

def _exec_env_to_top_map(exec_env):
    """
    Given a list of execution environments, return a map that indicates for
    each one which top it corresponds to.

    For this to work, this macros expects that all executions environments satisfy
    one of the two following requirements:
    - either they must be defined in the corresponding top's directory, e.g.
      //hw/top_earlgrey:<name_of_exec_env>. This directory is determined from the path
      of the top's hjson created by topgen.
    - or the target name must start with "top_<topname>", e.g.
      top_earlgrey_fpga_cw310_sival_rom_ext_no_hyper
    """
    top_map = {}
    for top in ALL_TOPS:
        # Extract the top's package from the hjson path.
        suffix = "/data/autogen:top_{}.gen.hjson".format(top.name)
        if not top.hjson.endswith(suffix):
            fail("top {}'s hjson does not end with the expected suffix".format(top.name))
        pkg = top.hjson.removesuffix(suffix)
        top_map[pkg] = top.name

    ev_map = {}
    for env in exec_env:
        (pkg, target) = env.split(":")

        # Remove @ if starting with @//
        if pkg.startswith("@//"):
            pkg = pkg[1:]
        if pkg in top_map:
            ev_map[env] = top_map[pkg]
        else:
            # Check if the target name starts with top_<topname>
            for top in ALL_TOPS:
                if target.startswith("top_" + top.name):
                    ev_map[env] = top.name

            # Check if we found one
            if env not in ev_map:
                fail("exec env {} does not match any known top. See _exec_env_to_top_map() for details".format(env))
    return ev_map

# Note about multitop behaviour:
# This rules allows `exec_env` to list execution environments from multiple tops.
# It will automatically filter the relevant ones based on the value of //hw/top:top.
# This means that the targets created by opentitan_binary() will expose only the
# binaries which can be compiled for the active top.
#
# See _exec_env_to_top_map() for constraints on the exec_env for this work.
def opentitan_binary(name, exec_env, **kwargs):
    # Filter execution environments by top.
    ev_map = _exec_env_to_top_map(exec_env)
    select_map = {}
    for ev in exec_env:
        topname = ev_map[ev]
        select_map[topname] = select_map.get(topname, []) + [ev]

    kwargs["target_compatible_with"] = \
        kwargs.get("target_compatible_with", []) + \
        opentitan_select_top(
            {
                top: []
                for top in select_map.keys()
            },
            ["@platforms//:incompatible"],
        )

    _opentitan_binary(
        name = name,
        exec_env = opentitan_select_top(select_map, []),
        **kwargs
    )

# Note about multitop behaviour:
# This rules allows `exec_env` to list execution environments from multiple tops.
# It will automatically filter the relevant ones based on the value of //hw/top:top.
# This means that the targets created by opentitan_test() will expose only the
# test which can be compiled/run for the active top.
#
# See _exec_env_to_top_map() for constraints on the exec_env for this work.

def opentitan_test(
        name,
        srcs = [],
        kind = "flash",
        deps = [],
        copts = [],
        defines = [],
        local_defines = [],
        includes = [],
        linkopts = [],
        linker_script = None,
        ecdsa_key = None,
        rsa_key = None,
        spx_key = None,
        manifest = None,
        exec_env = {},
        fpga = _fpga_params(),
        dv = _dv_params(),
        silicon = _silicon_params(),
        verilator = _verilator_params(),
        qemu = _qemu_params(),
        data = [],
        run_in_ci = None,
        **kwargs):
    """Instantiate a test per execution environment.

    Args:
      name: The base name of the test.  The name will be extended with the name
            of the execution environment.
      srcs: The source files for this test.
      kind: The kind of test (flash, ram, rom).
      deps: Dependecies for this test.
      copts: Compiler options for this test.
      defines: Compiler defines for this test.
      local_defines: Compiler defines for this test.
      includes: Additional compiler include dirs for this test.
      linker_script: Linker script for this test.
      ecdsa_key: ECDSA key to sign the binary for this test.
      rsa_key: RSA key to sign the binary for this test.
      spx_key: SPX key to sign the binary for this test.
      manifest: manifest used during signing for this test.
      linkopts: Linker options for this test.
      exec_env: A dictionary of execution environments.  The keys are labels to
                execution environments.  The values are the kwargs parameter names
                of the exec_env override or None.  If None, the default parameter
                names of `fpga`, `dv`, `silicon`, or `verilator` will be guessed.
      fpga: Execution overrides for a ChipWhisperer FPGA-based test.
      dv: Execution overrides for a DV-based test.
      silicon: Execution overrides for a silicon-based test.
      verilator: Execution overrides for a verilator-based test.
      qemu: Execution overrides for a QEUM-based test.
      run_in_ci: Override the automatic selection of execution environments to run in CI and run exactly those environments.
      kwargs: Additional execution overrides identified by the `exec_env` dict.
    """
    test_parameters = {
        "cw310": fpga,
        "fpga": fpga,
        "dv": dv,
        "silicon": silicon,
        "verilator": verilator,
        "qemu": qemu,
    }
    test_parameters.update(kwargs)
    kwargs_unused = kwargs.keys()

    # Build a map from execution environment to test parameters.
    # Find all exec_env which are not marked as broken at the same time.
    env_to_tparam = {}
    non_broken_exec_env = []
    for (env, pname) in exec_env.items():
        pname = _parameter_name(env, pname)

        # Temporary fallback to "cw310" if "fpga" parameters were not provided.
        # Prevents merge skew problems while the default parameter name changes.
        if pname == "fpga" and pname not in kwargs_unused:
            pname = "cw310"
        if pname in kwargs_unused:
            kwargs_unused.remove(pname)
        if pname not in test_parameters:
            fail("execution environment {} wants test parameters '{}' but those are not specified".format(env, pname))
        env_to_tparam[env] = test_parameters[pname]
        if not "broken" in env_to_tparam[env].tags:
            non_broken_exec_env.append(env)

    # Make sure that we used all elements in kwargs.
    if len(kwargs_unused) > 0:
        fail("the following arguments passed to opentitan_test were not used: {}".format(", ".join(kwargs_unused)))

    # Compute set of exec_env that should be marked as skip_in_ci.
    if run_in_ci == None:
        skip_in_ci = sets.make(ci_orchestrator(name, non_broken_exec_env))
        all_envs = sets.make(exec_env.keys())
        run_in_ci = sets.difference(all_envs, skip_in_ci)
    else:
        run_in_ci = sets.make(run_in_ci)

    # List of test parameters and how they map to the _opentitan_test attributes
    # and which default values they use if not present.
    TEST_PARAM_ATTRS = {
        # _opentitan_test attr -> (test param field name, default value)
        "defines": ("defines", []),
        "tags": ("tags", []),
        "timeout": ("timeout", None),
        "test_harness": ("test_harness", None),
        "binaries": ("binaries", {}),
        "rom": ("rom", None),
        "rom_ext": ("rom_ext", None),
        "otp": ("otp", None),
        "bitstream": ("bitstream", None),
        "post_test_cmd": ("post_test_cmd", ""),
        "post_test_harness": ("post_test_harness", None),
        "test_cmd": ("test_cmd", ""),
        "data": ("data", []),
        "param": ("param", None),
        "needs_jtag": ("needs_jtag", False),
    }

    # Precompute parameters.
    all_test_kwargs = {}
    for (env, tparam) in env_to_tparam.items():
        test_args = {}

        # Copy all arguments from the test params into the arguments.
        for (arg, (targ, default)) in TEST_PARAM_ATTRS.items():
            test_args[arg] = getattr(tparam, targ, default)
        if pname in kwargs_unused:
            kwargs_unused.remove(pname)

        # Modify test parameters to account for global parameters.
        test_args["defines"] = defines + test_args["defines"]
        test_args["data"] = data + test_args["data"]
        test_args["tags"] = test_args["tags"] + _hacky_tags(env)

        # Tag test if it must not run in CI.
        if not sets.contains(run_in_ci, env):
            test_args["tags"].append("skip_in_ci")
        all_test_kwargs[env] = test_args

    # With multitop, it is possible to have several exec_env with the same suffix
    # but which belong to different tops, e.g. //hw/top_earlgrey:sim_dv and
    # //hw/top_darjeeling:sim_dv. In this case, we still create a single
    # test call "<testname>_<sim_dv>" but the definition will use select() statements
    # based on the top. To do that, first we precompute a map from suffixes to list
    # of exec env.
    suffix_map = {}
    for env in exec_env:
        (_, suffix) = env.split(":")
        suffix_map[suffix] = suffix_map.get(suffix, []) + [env]
    ev_to_top_map = _exec_env_to_top_map(exec_env)

    all_tests = []
    for (suffix, env_list) in suffix_map.items():
        # Build a list of kwargs with select statements in them.
        test_kwargs = {}
        test_kwargs["exec_env"] = opentitan_select_top(
            {
                ev_to_top_map[env]: env
                for env in env_list
            },
            None,
        )
        test_kwargs["target_compatible_with"] = opentitan_select_top(
            {
                ev_to_top_map[env]: []
                for env in env_list
            },
            ["@platforms//:incompatible"],
        )
        for (arg, (_, default)) in TEST_PARAM_ATTRS.items():
            # Some attributes are not configurable and therefore cannot use
            # a select statement. For those, simply check that all cases are
            # the same.
            if arg in ["tags", "timeout"]:
                first_val = None
                first_env = None
                for env in env_list:
                    v = all_test_kwargs[env][arg]
                    if first_val == None:
                        first_val, first_env = v, env
                    elif first_val != v:
                        fail("attribute {} is not configurable and must have the same values for the following exec_env: {}".format(arg, env_list))
                test_kwargs[arg] = first_val
            else:
                select_args = {
                    ev_to_top_map[env]: all_test_kwargs[env][arg]
                    for env in env_list
                }
                test_kwargs[arg] = opentitan_select_top(select_args, default)

        test_name = "{}_{}".format(name, suffix)
        all_tests.append(":" + test_name)
        _opentitan_test(
            name = test_name,
            srcs = srcs,
            kind = kind,
            deps = deps,
            copts = copts,
            local_defines = local_defines,
            includes = includes,
            linker_script = linker_script,
            linkopts = linkopts,
            naming_convention = "{name}",
            ecdsa_key = ecdsa_key,
            rsa_key = rsa_key,
            spx_key = spx_key,
            manifest = manifest,
            **test_kwargs
        )

    native.test_suite(
        name = name,
        tests = all_tests,
        tags = ["manual"],
    )
