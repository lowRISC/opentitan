# Silicon Creator ROM Hooks

## Overview

The OpenTitan ROM defines pre-run and post-run hooks for any defined ROM state.

When transitioning to a ROM state, the ROM state machine first executes the pre-run hook.

The state's run callback is called only if the pre-run hook does not return an error.
Finally, the post-run hook runs upon successful termination of the ROM state's run callback:

```
│                      │
│   ┌──────────────┐   │
│   │Post-run Hook │   │
│   └───────┬──────┘   │
└───────────┼──────────┘
            │
            │
┌───────────┼──────────┐
│ ROM       │          │
│ State     │          │
│   ┌───────▼──────┐   │
│   │ Pre-run Hook │   │
│   └───────┬──────┘   │
│           │          │
│           │          │
│   ┌───────▽──────┐   │
│   │ Run Callback │   │
│   └───────┬──────┘   │
│           │          │
│           │          │
│   ┌───────▽──────┐   │
│   │Post-run Hook │   │
│   └───────┬──────┘   │
└───────────┼──────────┘
            │
            │
┌───────────┼──────────┐
│   ┌───────▼──────┐   │
│   │ Pre-run Hook │   │
│   └──────────────┘   │
│                      │

```

The transition from one ROM state to the next one is defined by the current ROM state's run callback:

``` c
rom_error_t rom_state_run_cb(void *arg, rom_state_t *next_state);
```

By default, the pre-run and post-run hooks do nothing. However, they provide a mechanism for silicon creators to override them with external implementations (e.g. with closed-source, vendor-specific initialization sequences).

Each ROM state pre-run and post-run hooks are defined as weak symbols using a pre-defined naming scheme.

For example the hooks prototypes for a ROM state named `kRomStateInit` would be:

``` c
OT_WARN_UNUSED_RESULT rom_error_t rom_state_pre_kRomStateInit(void *arg);
OT_WARN_UNUSED_RESULT rom_error_t rom_state_post_kRomStateInit(void *arg);
```

The ROM state API provides `C` macros that simplify the process of binding hook implementations to their corresponding states. Using these macros, the above implementation example would be replaced with the more maintainable form below:

``` c
OT_WARN_UNUSED_RESULT rom_error_t my_rom_init_pre_hook(void *arg) {
  ...
  return kErrorOk;
}
// The `kRomStateInit` pre-run hook is `my_rom_init_pre_hook`.
ROM_STATE_PRE_HOOK(kRomStateInit, my_rom_init_pre_hook);

OT_WARN_UNUSED_RESULT rom_error_t my_rom_init_post_hook(void *arg) {
  ...
  return kErrorOk;
}
// The `kRomStateInit` post-run hook is `my_rom_init_post_hook`.
ROM_STATE_POST_HOOK(kRomStateInit, my_rom_init_post_hook);
```

## ROM State Hooks Implementation

Downstream silicon creators can override the default pre-run and post-run hooks from an external, possibly closed-source repository.

A downstream ROM hooks repository should follow the layout defined in this example.

In particular, the repository must include:

- A `MODULE.bazel` file that defines a `rom_hooks` module: `module(name = "rom_hooks")`.
- A `BUILD.bazel` file that defines a `rom_hooks` `cc_library` target.
- A C file implementing the desired ROM state hooks overrides.
  Hooks implementations must follow the prototype defined in `rom_state.h`.
  Binding a hook to a ROM state pre-run or post-run step is done through respectively the `ROM_STATE_PRE_HOOK` and `ROM_STATE_POST_HOOK` macros.
  See `dummy_rom_hooks.c` in this folder for a simple example.

To link an OpenTitan ROM image with external hooks override, use `bazel --override_module` to specify the local path of the hooks repository.

For example:

``` bash
./bazelisk.sh test --override_module=rom_hooks=<path/to/ROM_hooks> --test_output=streamed --cache_test_results=no //sw/device/silicon_creator/rom/e2e:rom_e2e_smoke_sim_verilator
```
