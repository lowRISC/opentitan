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

### DIF Guidance

The following rules must be followed by public DIF functions (those declared in
the DIF library's header file). Internal DIF functions (those declared `static`
and not declared in the DIF library's header file) should follow these rules but
there are some relaxations of these rules for them described at the end.

* DIF declarations must match their definitions exactly.
  * Scalar arguments must not be declared `const` or `volatile` (cv-qualified)
    in DIF signatures.

* DIFs must use enum return codes rather than booleans for reporting errors. If
  a DIF can either error or instead produce a value, it must return an enum
  return code, and use an out-parameter for returning the produced value.
  * DIF libraries must have a general return code enum called
    `dif_<ip>_result_t`. It must define the following constants (in this order):
    * `kDif<ip>Ok`, with value 0, to denote the call succeeded.
    * `kDif<ip>Error`, with value 1, to denote a non-specific error happened
      during the call. This is for the `default:` case of enum switches (as
      noted below), and for assertion errors (usually where the function has
      already caused side effects so `kDif<ip>BadArg` cannot be used).
    * `kDif<ip>BadArg`, with value 2, to denote that the caller supplied
      incorrect arguments. This value must only be returned if the function has
      not caused any side effects.
  * DIF libraries should define specific return code enums for operations that
    fail in more specific ways. These specific return code enums can be shared
    between multiple DIFs that fail in the same way.

    These more specific return code types must be named
    `dif_<ip>_<operation>_result_t`, and their constants must be prefixed with
    `kDif<ip><operation>`. `<operation>` need not correspond to a DIF name if
    the return codes are shared between DIFs.

    The first three constants in these specific enums must define the following
    constants:
    * `kDif<ip><operation>Ok`, with value `kDif<ip>Ok`,
    * `kDif<ip><operation>Error`, with value `kDif<ip>Error`, and
    * `kDif<ip><operation>BadArg`, with value `kDif<ip>BadArg`.

    Additional, specific return code constants must all be defined after
    these three general constants, and may cover more specific forms of the
    return codes defined above, including more specific reasons arguments are
    invalid.

  * DIFs must document the meaning of each return code constant, including the
    required ones above, with a Doxygen comment per declaration. This comment
    must include whether returning this error code could have left the hardware
    in an invalid or unrecoverable state.
    * If a DIF returns `kDif<ip>Error`, it must be assumed to have left
      the hardware in an invalid, unrecoverable state.
    * If a DIF returns `kDif<ip>BadArg`, it must leave the hardware in a valid
      and recoverable state. This is in addition to the rule that this value may
      only be returned if the function has not caused any side effects.
  * DIFs that cannot error and that do not return a value must return `void`.

* DIFs must check their arguments against preconditions using "guard
  statements". A guard statement is a simple if statement at the start of a
  function which only returns an error code if the preconditions are not met.
  Guard statements must cover the following checks:
  * DIFs must ensure their pointer arguments are non-null, unless that pointer
    is for an optional out-parameter. Arguments typed `mmio_region_t` are not
    pointers, and cannot meaningfully be checked for non-nullness.
  * DIFs must ensure, if they only accept a subset of an enum, that the argument
    is within that subset. However, DIFs should assume, for checking
    preconditions, that any enum argument is one of the enum constants.
  * DIFs must not have side-effects before any guard statements.

    Side-effects include (but are not limited to) writing to memory, including
    memory-mapped hardware, and modifying processor CSRs. This means returning
    early from a guard statement must not leave the hardware in an invalid or
    unrecoverable state.

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
