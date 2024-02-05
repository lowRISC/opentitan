# The OpenTitan DIF Library

A DIF is a "Device Interface Function". DIFs are low-level routines for
accessing the hardware functionality directly, and are agnostic to the
particular environment or context they are called from. The intention is that
DIFs are high-quality software artifacts which can be used during design
verification and early silicon verification.

Although DIFs are high-quality software artifacts, they are not a hardware
abstraction layer (HAL), nor do they follow the device driver model of
any particular operating system, and as such, **_DIFs are not intended
to be used by production firmware_**.  DIFs, in combination with the
hardware specification, may be illustrative for writing drivers, but should
not be considered drivers themselves.

This subtree provides headers and libraries known collectively as the DIF
libraries.

There is one DIF library per hardware IP, and each one contains the DIFs
required to actuate all of the specification-required functionality of the
hardware they are written for.

Each DIF library contains both auto-generated (which are checked-in to our
repository under the `autogen/` subtree), and manually-implemented DIFs (which
are not sub-foldered).

## Developing New DIFs

Developers should use the `util/make_new_dif.py` script to both auto-generate a
subset of DIFs, *and* instantiate some initial boilerplate templates that should
be subsequently edited. Specifically, the script will create:

1. auto-generated DIF code, including:
  * an auto-generated (private) DIF header, `autogen/dif_<ip>_autogen.h`, based
  on `util/make_new_dif/templates/dif_autogen.h.tpl`,
  * auto-generated DIF implementations, `autogen/dif_<ip>_autogen.c`, based on
  `util/make_new_dif/templates/dif_autogen.c.tpl`, and
  * auto-generated DIF unit tests (that test the auto-generated DIFs),
  `autogen/dif_<ip>_autogen_unittest.cc`, based on
  `util/make_new_dif/templates/dif_autogen_unittest.cc.tpl`.
2. boilerplate templates (that should be manually edited/enhanced) for the
   portion of the IP DIF library that is manually implemented, including:
  * a (public) header for the DIF, based on
  `util/make_new_dif/templates/dif_template.h.tpl`], and
  * a checklist for the DIF, based on `doc/project/sw_checklist.md.tpl`.

Only the second set of files will need checking and editing, but the templates
serve to avoid most of the copy/paste required, while keeping our DIF libraries
consistent across IPs.

Further documentation for the script is provided in the script's source.
Additionally, please invoke `util/make_new_dif.py --help` for detailed usage.

## Checklists

This directory also contains checklists for each DIF, in markdown format. They
are linked to from the [Hardware Dashboard](../../../../hw/README.md), in the
Development Stage column.

## DIF Style Guide

DIFs are very low-level software, so they have a more rigorous coding style than
other parts of the codebase.

DIFs should follow the [OpenTitan C/C++ style
guide](../../../../doc/contributing/style_guides/c_cpp_coding_style.md) where it does not
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
  libraries):
  * `sw/lib/sw/device/base/bitfield.h`
  * `sw/lib/sw/device/base/mmio.h`
  * `sw/lib/sw/device/base/memory.h`
  * `sw/ip/base/dif/dif_base.h`
* DIF libraries must not depend on other DIF libraries. Exercising DIF
  functionality may require an environment set up using another DIF library, but
  DIFs must not call DIFs in other DIF libraries.
* DIF library headers must be polyglot headers for C and C++.
* the public (manually-implemented) DIF header for each DIF library should
  `#include` the (private) auto-generated header, so that DIF consumers need
  only `#include` the public DIF header to make use of an IP's DIF library.

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
* All functions below are assumed to return `dif_result_t`, a global DIF return
  type defined in `sw/ip/base/dif/dif_base.h`.
* Unless otherwise noted, all symbols mentioned below are required.

#### Hardware Parameterization

Our aim is that a single DIF library can be used with multiple instances of the
same IP on the same chip, even when those IPs have been instantiated with
different hardware parameters.

At the moment, we have a good approach to being able to address separate
hardware instances instantiated at separate addresses, as long as they have the
same hardware parameters (see the `base_addr` member in `dif_<ip>_t`).
Most other parameters come from the specific IP on a case-by-case basis, and are
extracted from the IP's auto-generated register header file, e.g.,
`<ip>_regs.h`.

#### Base Types

There are two categories of base types:
1. those that are defined once in `sw/ip/base/dif/dif_base.h` and used in all
   DIF libraries, and
2. those that are expected to be defined separately by all DIF libraries (unless
   otherwise specified).

The base types defined in `sw/ip/base/dif/dif_base.h` include:
* `dif_result_t` -- an enum representing global DIF return codes.
* `dif_toggle_t` -- an enum to be used instead of a `bool` when describing
  enablement states.

The base types that are expected to be defined separately by all DIF libraries
include:
* `dif_<ip>_t` -- an **auto-generated** type representing a handle to the
  peripheral. Its first (and only) field is always the base address for the
  peripheral registers, styled `mmio_region_t base_addr;`.
  This type is usually passed by `const` pointer, except when it is
  being initialized (see `dif_<ip>_init()` below).
* `dif_<ip>_config_t` -- a **manually-defined** struct representing runtime
  configuration parameters for the peripheral. It is only present when
  `dif_<ip>_configure()` is defined. This type is always passed by value.

#### Lifecycle Functions
The following functions are the basic functionality for initializing and
handling the lifetime of a handle.

* `dif_result_t dif_<ip>_init(mmio_region_t base_addr, dif_<ip>_t *handle);`
  initializes `handle` with the base address of the instantiated IP this
  DIF is targeting to use. This DIF is **auto-generated**.

* `dif_result_t dif_<ip>_configure(const dif_<ip>_t *handle, dif_<ip>_config_t
  config);` configures the hardware managed by `handle` with runtime parameters
  in an implementation-defined way. This function should be "one-off": it should
  only need to be called once for the lifetime of the handle.
  _If there is no meaningful state to configure, this function may be omitted._
  In particular, DIF libraries providing transaction functions will usually have
  no need for this function at all. This DIF is **manually-implemented**.

#### Transaction Management

The following types and functions are the standard interface for
*transaction-oriented* peripherals, in which a client schedules an operation to
be completed at some point in the future. All types and functions listed here
are **manually-implemented**.

* `dif_<ip>_transaction_t` is a struct representing runtime parameters for
  starting a hardware transaction. It is only present when `dif_<ip>_start()` is
  defined. This type is always passed by value. A DIF library my opt to use
  another pre-existing type instead, when that type provides a more semantically
  appropriate meaning.
* `dif_<ip>_output_t` is a struct describing how to output a completed
  transaction. Often, this will be a type like `uint8_t *`. The same caveats
  about a DIF library providing a different type apply here.
* `dif_result_t dif_<ip>_start(const dif_<ip>_t *handle, dif_<ip>_transaction_t
  transaction);` starts a transaction on a transaction-oriented peripheral. This
  function may be called multiple times, but each call should be paired with a
  `dif_<ip>_end()` call.
* `dif_result_t dif_<ip>_end(const dif_<ip>_t *handle, dif_<ip>_output_t out);`
  completes a transaction started with `dif_<ip>_start()`, writing its results
  to a location specified in `out`.

If a peripheral supports multiple transaction modes with incompatible parameter
types, the above names may be duplicated by inserting `mode_<mode>` after `<ip>`.
For example,
```
dif_result_t dif_<ip>_mode_<mode>_end(const dif_<ip>_t *handle,
                                  dif_<ip>_mode_<mode>_output_t out);
```
There is no requirement that `_start()` and `_end()` share the same set of
`<mode>`s; for example, there might be a single `dif_<ip>_start()` but many
`dif_<ip>_mode_<mode>_end()`s. This style of API is preferred over using
`union`s with `dif_<ip>_transaction_t` and `dif_<ip>_output_t`.

#### Register Locking

The following functions are the standard interface for peripherals that can lock
portions of their software-accessible functionality. All types and functions
listed here are **manually-implemented**.

* `kDifLocked` is the global return result enum of an operation that can be
  locked out. DIFs which may fail due to lockout, which is software-detectable,
  should return this value when possible.
* `dif_result_t dif_<ip>_lock(const dif_<ip>_t *handle);` locks out all portions
  of the peripheral which can be locked. If a peripheral can be locked-out
  piecewise, `dif_<ip>_lock_<operation>()` functions may be provided alongside
  or in lieu of `dif_<ip>_lock()`.
* `dif_result_t dif_<ip>_is_locked(const dif_<ip>_t *handle, bool *is_locked);`
  checks whether the peripheral has been locked out. As with `dif_<ip>_lock()`,
  DIF libraries may provide a piecewise version of this API.

#### Interrupt Management

The following types and functions are the standard interface for peripherals that
provide a collection of `INTR_ENABLE`, `INTR_STATE`, and `INTR_TEST` registers
for interrupt management. A DIF library for a peripheral providing such
registers must provide this interface. To ensure this, all interrupt DIFs,
including: headers, (C) implementations, and unit tests, are *auto-generated* from
templates and an IP's HJSON configuration file using the `util/make_new_dif.py`
tool (described above).

If a peripheral is defined with `no_auto_intr_regs: true`, this exact API is not
required even if the `INTR_` registers are provided (though DIF libraries are
encouraged to follow it where it makes sense). _In these cases, auto-generated
interrupt DIFs may not exist._

* `dif_<ip>_irq_t` is an enum that lists all of the interrupt types for this
  peripheral. These derived from the `interrupt_list` attribute within an IP's
  HJSON file.
* `dif_result_t dif_<ip>_irq_get_state(const dif_<ip>_t *handle,
  dif_<ip>_irq_state_snapshot_t *snapshot, bool *is_pending);` returns a
  snapshot of the entire interrupt state register, to check the status of all
  interrupts for a peripheral.
* `dif_result_t dif_<ip>_irq_is_pending(const dif_<ip>_t *handle, dif_<ip>_irq_t
  irq, bool *is_pending);` checks whether a specific interrupt is
  pending (i.e., if the interrupt has been asserted but not yet cleared).
* `dif_result_t dif_<ip>_irq_acknowledge_all(const dif_<ip>_t *handle);`
  acknowledges all interrupts have been serviced, marking them as
  complete by clearing all pending bits. This function does nothing and returns
  `kDifOk` if no interrupts were pending.
* `dif_result_t dif_<ip>_irq_acknowledge(const dif_<ip>_t *handle, dif_<ip>_irq_t
  irq);` acknowledges that an interrupt has been serviced, marking it as
  complete by clearing its pending bit. This function does nothing and returns
  `kDifOk` if the interrupt wasn't pending.
* `dif_result_t dif_<ip>_irq_get_enabled(const dif_<ip>_t *handle, dif_<ip>_irq_t
  irq, const dif_<ip>_toggle_t *state);` gets whether an interrupt is
  enabled (i.e., masked).
* `dif_result_t dif_<ip>_irq_set_enabled(const dif_<ip>_t *handle, dif_<ip>_irq_t
  irq, dif_<ip>_toggle_t state);` sets whether a particular interrupt is
  enabled (i.e., masked).
* `dif_result_t dif_<ip>_irq_force(const dif_<ip>_t *handle, dif_<ip>_irq_t
  irq);` forcibly asserts a specific interrupt, causing it to be serviced
  as if hardware had triggered it.

Additionally, the following types allow for batch save/restore operations on
the interrupt enable register:

* `dif_<ip>_irq_enable_snapshot_t` is a type that encapsulates restorable
  interrupt enablement state, to be used with the two functions below. This type
  should be treated as opaque by clients.
* `dif_result_t dif_<ip>_irq_disable_all(const dif_<ip>_t *handle,
  dif_<ip>_irq_enable_snapshot_t *snapshot);` disables all interrupts associated
  with the peripheral, saving them to `*snapshot`. `snapshot` may be null, in
  which case the previous enablement state is not saved.
* `dif_result_t dif_<ip>_irq_restore_all(const dif_<ip>_t *handle,
  const dif_<ip>_irq_enable_snapshot_t *snapshot);` restores an interrupt
  enablement snapshot produced by the above function.

#### Unit Testing

Each DIF has an associated unit test, written in C++. For auto-generated DIFs,
their associated unit tests are also auto-generated. For manually-implemented
DIFs, their associated unit tests follow the conventions:
* The whole file is wrapped in the `dif_<ip>_unittest` namespace.
* There is a base class for all test fixtures, named `<ip>Test`, which derives
  `testing::Test` and `mock_mmio::MmioTest`.
* Each function has an associated test fixture, usually named
  `<function>Test`, which derives `<ip>Test`. Multiple similar functions may be
  grouped under one fixture.
* Prefer to use expectation macros, like `EXPECT_DIF_OK`, defined in
  `dif_test_base.h` whenever possible (e.g. do not write
  `EXPECT_EQ(<long expression>, kDifOk);`).

### DIF Style Guidance

The following rules must be followed by public DIF functions (those declared in
the DIF library's header file). Internal DIF functions (those declared `static`
and not declared in the DIF library's header file) should follow these rules but
there are some relaxations of these rules for them described at the end.

* DIF declarations must match their definitions exactly.
  * Scalar arguments must not be declared `const` or `volatile` (cv-qualified)
    in DIF signatures.

* DIFs must use one of the `dif_result_t` enums (described in
  `sw/ip/base/dif/dif_base.h`) rather than booleans for reporting errors. If
  a DIF can either error or instead produce a value, it must return a
  `dif_result_t`, and use an out-parameter for returning the produced value.
  * DIFs that return an enum return code must be annotated with
    `OT_WARN_UNUSED_RESULT`, to help minimize mistakes from
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
    this should return `kDifError` or the equivalent return code value from
    a global DIF return code enum. If the enum switch is part of a guard
    statement, it may return `kDifBadArg` instead.
  * Enum switches do not need a `case` for enum constants that are unreachable
    due to a guard statement.

* DIFs must use `sw/lib/sw/device/base/mmio.h` for accessing memory-mapped
  hardware. DIFs must not use `sw/lib/sw/device/base/memory.h` for accessing
  memory-mapped hardware.

* Internal DIF functions, which are not intended to be part of a public DIF
  library interface, must not be declared in the DIF library header, and must be
  marked `static`.
  * `static` DIF functions should not be marked `static inline`.
  * An internal DIF function does not need to check preconditions, if all the
    DIF functions that call it have already checked that precondition.
