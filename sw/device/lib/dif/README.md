# The OpenTitan DIF Library

A DIF is a "Device Interface Function". DIFs are low-level routines for
accessing the hardware functionality directly, and are agnostic to the
particular environment or context they are called from. The intention is that
DIFs can be used during design verification, and during early silicon
verification, and by the high-level driver software in production firmware.

This subtree provides headers and libraries known collectively as the DIF
libraries.

There is one DIF library per hardware IP, and each one contains the DIFs
required to actuate all of the specification-required functionality of the
hardware they are written for.

## New DIFs

Developers should use the `util/make_new_dif.py` script to instantiate some
DIF-related templates which follow the guidance below. The script will create:

*   A Header for the DIF, based on [`dif_template.h.tpl`](./dif_template.h.tpl).
*   A Checklist for the DIF, based on `doc/project/sw_checklist.md.tpl`.

These files will need checking and editing, but the templates serve to avoid
most of the copy/paste required.

Further documentation for the script is provided in the script's source.

## Checklists

This directory also contains checklists for each DIF, in markdown format. They
are linked to from the [Hardware Dashboard]({{< relref "hw" >}}), in the
Development Stage column.

## DIF Style Guide

DIFs are very low-level software, so they have a more rigorous coding style than
other parts of the codebase.

DIFs should follow the [OpenTitan C/C++ style
guide](https://docs.opentitan.org/doc/rm/c_cpp_coding_style/) where it does not
contradict with the guidelines below.

The guidelines below apply to writing DIFs, and code should be written in a
similar style to the existing DIF libraries in this directory.

### Definitions

<a name="side-effects"></a>
**Side-effects** include (but are not limited to) writing to memory, including
memory-mapped hardware, and modifying processor CSRs.

### DIF Library Guidance

* DIF libraries must be written in C.
* DIF libraries can only depend on the following headers (and their associated
  libraries) from the `sw/device/lib/base` directory:
  * `sw/device/lib/base/bitfield.h`
  * `sw/device/lib/base/mmio.h`
  * `sw/device/lib/base/memory.h`
* DIF libraries must not depend on other DIF libraries. Exercising DIF
  functionality may require an environment set up using another DIF library, but
  DIFs must not call DIFs in other DIF libraries.
* DIF library headers must be polyglot headers for C and C++.

### DIF API Guidance

The following rules specify the basic API that each DIF must conform to. These
rules specify the names of types, constants, and functions that each DIF must
define for providing certain kinds of non-device-specific functionality (such as
initializing handles or managing interrupts).

Notational caveats:
* The token `<ip>` is the "short IP name" of the peripheral,
  in `snake_case` or `PascalCase` as is appropriate.
* The parameter name `handle` is not normative, and DIF libraries are free to
  choose a different, but consistent, name for it.
* All functions below are assumed to return `dif_<ip>_result_t` or
  `dif_<ip>_<operation>_result_t`, so their return values are specified as
  `result_t`.
* Unless otherwise noted, all symbols mentioned below are required.


#### Hardware Parameterization

Our aim is that a single DIF library can be used with multiple instances of the
same IP on the same chip, even when those IPs have been instantiated with
different hardware parameters.

At the moment, we have a good approach to being able to address separate
hardware instances instantiated at separate addresses, as long as they have the
same hardware parameters (see the `base_addr` member in `dif_<ip>_params_t`).
Most other parameters come from the specific IP on a case-by-case basis.

As much as possible, we would like to hide these parameters underneath the
interface of the DIF, but this is not always possible, especially where
particular functionality requires the DIF caller to allocate memory. This should
be done even if the current DIF implementation does not support changing
parameters, so we can add this parameterization later.

In order to support exposing these parameters to callers, DIFs should provide
query functions which take a `dif_<ip>_params_t`, rather than `#define`s or
global variable definitions. These functions do not have to return
`dif_<ip>_result_t` if they do not error.

An example of such a query function is provided in the template, called
`dif_<ip>_get_size`, but we are not placing restrictions on the naming of these
functions.

One implication of this decision is that we will not always be able to provide
struct definitions containing fixed-size buffers, which we have relied upon in
the past. These structs should instead use a pointer and a size member to safely
store the buffer outside the struct and use it without overflows. From the DIF's
perspective, these buffers are dynamically allocated, even if we get static
information about their size from other information (e.g. topgen).


#### Base Types

The following basic types are expected to be provided by all DIFs (unless
otherwise specified).

* `dif_<ip>_t` is a type representing a handle to the peripheral. Its fields
  are private implementation details, and should not be read or written to by
  clients. This type is usually passed by `const` pointer, except when it is
  being initialized (see `dif_<ip>_init()` below).
* `dif_<ip>_params_t` is a struct representing hardware instantiation parameters
  that a DIF library cannot know in advance. Its first field is always the
  base address for the peripheral registers, styled `mmio_region_t base_addr;`.
  This type is always passed by value.
* `dif_<ip>_config_t` is a struct representing runtime configuration
  parameters. It is only present when `dif_<ip>_configure()` is defined.
  This type is always passed by value.
* `dif_<ip>_result_t` is an enum representing general return codes for DIFs. It
  must define the following constants, in order:
    * `kDif<ip>Ok`, with value 0, to denote the call succeeded.
    * `kDif<ip>Error`, with value 1, to denote a non-specific error happened
      during the call. This is for the `default:` case of enum switches (as
      noted below), and for assertion errors (usually where the function has
      already caused side-effects so `kDif<ip>BadArg` cannot be used).
    * `kDif<ip>BadArg`, with value 2, to denote that the caller supplied
      incorrect arguments. This value must only be returned if the function has
      not caused any side-effects.
* `dif_<ip>_<operation>_result_t` is an enum representing more specific failure
  modes. These specific return code enums can be shared between multiple DIFs
  that fail in the same way. `<operation>` need not correspond to a DIF name if
  more than one DIF uses these return codes.

  The first three constants in these specific enums must define the following
  constants:
  * `kDif<ip><operation>Ok`, with value `kDif<ip>Ok`,
  * `kDif<ip><operation>Error`, with value `kDif<ip>Error`, and
  * `kDif<ip><operation>BadArg`, with value `kDif<ip>BadArg`.

  Additional, specific return code constants must all be defined after
  these three general constants, and may cover more specific forms of the
  return codes defined above, including more specific reasons arguments are
  invalid.
* `dif_<ip>_toggle_t` is an enum representing an enabled or disabled state. This
  must define exactly two constants, in no particular order:
  * `kDif<ip>ToggleEnable`, indicating an enabled state.
  * `kDif<ip>ToggleDisable`, indicating an enabled state.

  This type is intended to be used as a better-named replacement for `bool`,
  for operations which are setting wither a behavior is enabled or disabled
  (such as whether an interrupt is maskable). Values of this type should *not* be
  used as `if`-statement conditions.

  If no function requires this type, it may be omitted.

#### Lifecycle Functions
The following functions are the basic functionality for initializing and
handling the lifetime of a handle.

* `result_t dif_<ip>_init(dif_<ip>_params_t params, dif_<ip>_t *handle);`
  initializes `handle` in an implementation-defined way, but does not perform any
  hardware operations. `handle` may point to uninitialized data on function entry,
  but if the function returns `Ok`, then `handle` must point to initialized data.
* `result_t dif_<ip>_configure(const dif_<ip>_t *handle, dif_<ip>_config_t
  config);` configures the hardware managed by `handle` with runtime parameters
  in an implementation-defined way. This function should be "one-off": it should
  only need to be called once for the lifetime of the handle.

  If there is no meaningful state to configure, this function may be omitted.
  In particular, DIF libraries providing transaction functions will usually have
  no need for this function at all.

#### Transaction Management

The following types and functions are the standard interface for
*transaction-oriented* peripherals, in which a client schedules an operation to
be completed at some point in the future.

* `dif_<ip>_transaction_t` is a struct representing runtime parameters for
  starting a hardware transaction. It is only present when `dif_<ip>_start()` is
  defined. This type is always passed by value. A DIF library my opt to use
  another pre-existing type instead, when that type provides a more semanticly
  appropriate meaning.
* `dif_<ip>_output_t` is a struct describing how to output a completed
  transaction. Often, this will be a type like `uint8_t *`. The same caveats
  about a DIF library providing a different type apply here.
* `result_t dif_<ip>_start(const dif_<ip>_t *handle, dif_<ip>_transaction_t
  transaction);` starts a transaction on a transaction-oriented peripheral. This
  function may be called multiple times, but each call should be paired with a
  `dif_<ip>_end()` call.
* `result_t dif_<ip>_end(const dif_<ip>_t *handle, dif_<ip>_output_t out);`
  completes a transaction started with `dif_<ip>_start()`, writing its results
  to a location specified in `out`.

If a peripheral supports multiple transaction modes with incompatible parameter
types, the above names may be duplicated by inserting `mode_<mode>` after `<ip>`.
For example,
```
result_t dif_<ip>_mode_<mode>_end(const dif_<ip>_t *handle,
                                  dif_<ip>_mode_<mode>_output_t out);
```
There is no requirement that `_start()` and `_end()` share the same set of
`<mode>`s; for example, there might be a single `dif_<ip>_start()` but many
`dif_<ip>_mode_<mode>_end()`s. This style of API is prefered over using
`union`s with `dif_<ip>_transaction_t` and `dif_<ip>_output_t`.

#### Register Locking

The following functions are the standard interface for peripherals that can lock
portions of their software-accessible functionality.

* `kDif<ip><operation>Locked` is the standard variant name for the result enum
  of an operation that can be locked out. DIFs which may fail due to lockout,
  which is software-detectable, should return this value when possible.
* `result_t dif_<ip>_lock(const dif_<ip>_t *handle);` locks out all portions of
  the peripheral which can be locked. If a peripheral can be locked-out
  piecewise, `dif_<ip>_lock_<operation>()` functions may be provided alonside or
  in lieu of `dif_<ip>_lock()`.
* `result_t dif_<ip>_is_locked(const dif_<ip>_t *handle, bool *is_locked);`
  checks whether the peripheral has been locked out. As with `dif_<ip>_lock()`,
  DIF libraries may provide a piecewise version of this API.

#### Interrupt Management

The following types and functions are the standard interface for peripherals that
provide a collection of `INTR_ENABLE`, `INTR_STATE`, and `INTR_TEST` registers
for interrupt management. A DIF library for a peripheral providing such
registers must provide this interface.

If a peripheral is defined with `no_auto_intr_regs: true`, this exact API is not
required even if the `INTR_` registers are provided (though DIF libraries are
encouraged to follow it where it makes sense).

* `dif_<ip>_irq_t` is an enum that lists all of the interrupt types for this
  peripheral. A DIF library may opt to use another pre-existing type instead,
  when, for example, interrupt types are coupled to a distinct
  peripheral-specific concept. In that case, all occurrences of `dif_<ip>_irq_t`
  below should be replaced with this type.
* `result_t dif_<ip>_irq_is_pending(const dif_<ip>_t *handle, dif_<ip>_irq_t
  irq, bool *is_pending);` checks whether a specific interrupt is
  pending (i.e., if the interrupt has been asserted but not yet cleared).
* `result_t dif_<ip>_irq_acknowledge(const dif_<ip>_t *handle, dif_<ip>_irq_t
  irq);` acknowledges that an interrupt has been serviced, marking it as
  complete by clearing its pending bit. This function does nothing and returns
  `Ok` if the interrupt wasn't pending.
* `result_t dif_<ip>_irq_get_enabled(const dif_<ip>_t *handle, dif_<ip>_irq_t
  irq, const dif_<ip>_toggle_t *state);` gets whether an interrupt is
  enabled (i.e., masked).
* `result_t dif_<ip>_irq_set_enabled(const dif_<ip>_t *handle, dif_<ip>_irq_t
  irq, dif_<ip>_toggle_t state);` sets whether a particular interrupt is
  enabled (i.e., masked).
* `result_t dif_<ip>_irq_force(const dif_<ip>_t *handle, dif_<ip>_irq_t
  irq);` forcibly asserts a specific interrupt, causing it to be serviced
  as if hardware had triggered it.

Additionally, the following types allow for batch save/restore operations on
the interrupt enable register:

* `dif_<ip>_irq_snapshot_t` is a type that encapsulates restorable interrupt
  state, to be used with the two functions below. This type should be treated as
  opaque by clients.
* `result_t dif_<ip>_irq_disable_all(const dif_<ip>_t *handle,
  dif_<ip>_irq_snapshot_t *snapshot);` disables all interrupts associated with
  the peripheral, saving them to `*snapshot`. `snapshot` may be null, in which
  case the previous enablement state is not saved.
* `result_t dif_<ip>_irq_restore_all(const dif_<ip>_t *handle,
  const dif_<ip>_irq_snapshot_t *snapshot);` restores an interrupt enablement snapshot
  produced by the above function.

#### Unit Testing

Each DIF has an associated unit test, written in C++. Those tests follow the
following conventions:
* The whole file is wrapped in the `dif_<ip>_unittest` namespace.
* There is a base class for all test fixtures, named `<ip>Test`, which derives
  `testing::Test` and `mock_mmio::MmioTest`.
* Each function has an associated test fixture, usually named
  `<function>Test`, which derives `<ip>Test`. Multiple similar functions may be
  grouped under one fixture.

### DIF Style Guidance

The following rules must be followed by public DIF functions (those declared in
the DIF library's header file). Internal DIF functions (those declared `static`
and not declared in the DIF library's header file) should follow these rules but
there are some relaxations of these rules for them described at the end.

* DIF declarations must match their definitions exactly.
  * Scalar arguments must not be declared `const` or `volatile` (cv-qualified)
    in DIF signatures.

* DIFs must use one of the `result_t` enums described above rather than booleans
  for reporting errors. If a DIF can either error or instead produce a value, it
  must return a `result_t`, and use an out-parameter for returning the produced
  value.
  * DIFs must document the meaning of each return code constant, including the
    required ones above, with a Doxygen comment per declaration. This comment
    must include whether returning this error code could have left the hardware
    in an invalid or unrecoverable state.
    * If a DIF returns `kDif<ip>Error`, it must be assumed to have left
      the hardware in an invalid, unrecoverable state.
    * If a DIF returns `kDif<ip>BadArg`, it must leave the hardware in a valid
      and recoverable state. This is in addition to the rule that this value may
      only be returned if the function has not caused any side-effects.
  * DIFs that return an enum return code must be annotated with
    `__attribute__((warn_unused_result))`, to help minimize mistakes from
    failing to check a result. This guidance applies to `static` helper
    functions that return an error of some kind as well.
  * DIFs that cannot error and that do not return a value must return `void`.

* DIFs must check their arguments against preconditions using "guard
  statements". A guard statement is a simple if statement at the start of a
  function which only returns an error code if the preconditions are not met.
  Guard statements must cover the following checks:
  * DIFs must ensure their pointer arguments are non-null, unless that pointer
    is for an optional out-parameter. Arguments typed `mmio_region_t` are not
    pointers, and cannot meaningfully be checked for non-nullness.
  * DIFs must ensure, if they only accept a subset of an enum, that the argument
    is within that subset. However, DIFs may assume, for checking preconditions,
    that any enum argument is one of the enum constants.
  * DIFs must not cause any side-effects before any guard statements. This means
    returning early from a guard statement must not leave the hardware in an
    invalid or unrecoverable state.

* Switch statements in DIFs must always have a default case, including when
  switching on an enum value (an "enum switch").
  * The default case of an enum switch must report an error for values that are
    not a constant from that enum. In the absence of more specific information,
    this should return `kDif<ip>Error` or the equivalent return code value from
    a more specific return code enum. If the enum switch is part of a guard
    statement, it may return `kDif<ip>BadArg` instead.
  * Enum switches do not need a `case` for enum constants that are unreachable
    due to a guard statement.

* DIFs must use `sw/device/lib/base/mmio.h` for accessing memory-mapped
  hardware. DIFs must not use `sw/device/lib/base/memory.h` for accessing
  memory-mapped hardware.

* Internal DIF functions, which are not intended to be part of a public DIF
  library interface, must not be declared in the DIF library header, and must be
  marked `static`.
  * `static` DIF functions should not be marked `static inline`.
  * An internal DIF function does not need to check preconditions, if all the
    DIF functions that call it have already checked that precondition.
