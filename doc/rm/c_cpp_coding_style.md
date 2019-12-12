---
title: "C and C++ Coding Style Guide"
---

## Basics

### Summary

C and C++ are widely used languages for (embedded) software.

Our C and C++ style guide follows the [Google C++ Style Guide](https://google.github.io/styleguide/cppguide.html), with some exceptions and clarifications.

As with all style guides the intention is to:
*   promote consistency across projects
*   promote best practices
*   increase code sharing and re-use


### Terminology Conventions

Unless otherwise noted, the following terminology conventions apply to this
style guide:

*   The word ***must*** indicates a mandatory requirement.
    Similarly, ***do not*** indicates a prohibition.
    Imperative and declarative statements correspond to ***must***.
*   The word ***recommended*** indicates that a certain course of action is preferred or is most suitable.
    Similarly, ***not recommended*** indicates that a course of action is unsuitable, but not prohibited.
    There may be reasons to use other options, but the implications and reasons for doing so must be fully understood.
*   The word ***may*** indicates a course of action is permitted and optional.
*   The word ***can*** indicates a course of action is possible given material, physical, or causal constraints.

## Shared C and C++ Style Guide

We use the [Google C++ Style Guide](https://google.github.io/styleguide/cppguide.html) for both C and C++ code.
The following exceptions and additions to this style guide apply to both C and C++ code.

### Pointers

***When declaring pointer types, the asterisk (`*`) should be placed next to the variable name, not the type.***

Example:

```c
int *ptr;
```

### Formatting of loops and conditionals

***Single-statement blocks are not allowed. All conditions and loops must use braces.***

Example:
```c
if (foo) {
  do_something();
}
```

### Comments

***Comments should be `// C99-style` for consistency with C++.***

***Variables mentioned in comments should be delimited with pipe (`|`) characters.***

Example:

```c
// |ptr| can never be NULL for reasons.
```

### TODO Comments
***TODO comments should be in the format `TODO: message`.***

***TODO comments which require more explanation should reference an issue.***

It is recommended to use fully-qualified issue numbers or URLs when referencing issues or pull requests.

TODO comments should not indicate an assignee of the work.

Example:

```c
// TODO: This algorithm should be rewritten to be more efficient.
// (Bug lowrisc/reponame#27)
```

### Included files

***`#include` directives must, with exceptions, be rooted at `$REPO_TOP`.***

Every `#include` directive must be rooted at the repository base, including files in the same directory.
This helps the reader quickly find headers in the repository, without having to worry about local include-search rules.

Example: `my/device/library.c` would start with a directive like the following:

```c
#include "my/device/library.h"
```

This rule does not apply to generated headers, since they do not yet have a designated location in the source tree, and are instead included from ad-hoc locations.
Until these questions are resolved, these includes must be marked as follows:
```c
#include "my_generated_file.h"  // Generated.
```
This convention helps readers distinguish which files they should not expect to find in-tree.

The above rules also do not apply to system includes, which should be included by the names dictated by the ISO standard, e.g. `#include <stddef.h>`.


### Public function (API) documentation

***It is recommended to document public functions, classes, methods, and data structures in the header file with a Doxygen-style comment.***

The first line of the comment is the summary, followed by a new line, and an optional longer description.
Input arguments and return arguments can be documented with `@param` and `@return` if they are not self-explanatory from the name.

Example:

```c
/**
 * Do something amazing
 *
 * Create a rainbow and place a unicorn at the bottom of it. @p arg1 pots of
 * gold will be positioned on the east end of the rainbow.
 *
 * @param pots_of_gold Number of gold pots to place next to the rainbow
 * @param unicorns Number of unicorns to position on the rainbow
 * @return 0 if the function was successful, -1 otherwise
 */
int create_rainbow(int pots_of_gold, int unicorns);
```

## C++ Style Guide

### C++ Version

C++ code should target C++14.


## C Style Guide

The [Google C++ Style Guide](https://google.github.io/styleguide/cppguide.html) targets C++, but it can also be used for C code with minor adjustments.
Consequently, C++-specific rules don't apply.
In addition to the shared C and C++ style guide rules outlined before, the following C-specific rules apply.

### C Version

***C code should target C11.***

The following nonstandard extensions may be used:
*   Inline assembly
*   Nonstandard attributes
*   Compiler builtins

It is recommended that no other nonstandard extensions are used.

Any nonstandard features that are used must be compatible with both GCC and Clang.

### Function, enum, struct and typedef naming

***Names of functions, `enum`s, `struct`s, and `typedef`s must be `lower_snake_case`.***

This rule deviates from the Google C++ style guide to align closer with a typical way of writing C code.

### Preprocessor Macros

Macros are often necessary and reasonable coding practice C (as opposed to C++) projects.
In contrast to the recommendation in the Google C++ style guide, exporting macros as part of the public API is allowed in C code.
A typical use case is a header with register definitions.

### Aggregate Initialization

C99 introduces designated initializers: when initializing a type of struct, array, or union type, it is possible to *designate* an initializer as being for a particular field or array index.
For example:
```c
my_struct_t s = { .my_field = 42 };
int arr[5] = { [3] = 0xff, [4] = 0x1b };
```
With judicious use, designated initializers can make code more readable and robust; struct field reordering will not affect downstream users, and weak typing will not lead to surprising union initialization.

When initializing a struct or union, initializers within *must* be designated; array-style initialization (or mixing designated and undesignated initializers) is forbidden.

Furthermore, the nested forms of designated initialization are forbidden (e.g., `.x.y = foo` and `.x[0] = bar`), to discourage initialization of deeply nested structures with flat syntax.
This may change if we find cases where this initialization improves readability.

When initializing an array, initializers *may* be designated when that makes the array more readable (e.g., lookup tables that are mostly zeroed). Mixing designated and undesignated initializers, or using nested initializers, is still
forbidden.

### Nonstandard Attributes

The following nonstandard attributes may be used:
*   `section(<name>)` to put a definition into a given object section.
*   `weak` to make a symbol definition have weak linkage.
*   `interrupt` to ensure a function has the right prolog and epilog for interrupts (this involves saving and restoring more registers than normal).
*   `packed` to ensure a struct contains no padding.

It is recommended that other nonstandard attributes are not used, especially where C11 provides a standard means to accomplish the same thing.

All nonstandard attributes must be supported by both GCC and Clang.

Nonstandard attributes must be written before the declaration, like the following example, so they work with both declarations and definitions.

```c
__attribute__((section(".crt"))) void _crt(void);
```

### Nonstandard Compiler Builtins

All nonstandard builtins must be supported by both GCC and Clang.
Compiler builtin usage is complex, and it is recommended that a compiler engineer reviews any code that adds new builtins.

In the following, `__builtin_foo` is the "prefixed" name and `foo` is the corresponding "unprefixed" name.

***The use of nonstandard compiler builtins must have an unprefixed compatible definition.***

There are two ways of doing this, depending on what the builtin does.

For builtins that correspond to a C library function, the unprefixed function must be available to the linker, as the compiler may still insert a call to this function.
Unfortunately, older versions of GCC do not support the `__has_builtin()` preprocessor function, so compiler detection of support for these builtins is next to impossible.
In this case, a standards-compliant implementation of the unprefixed name must be provided, and the compilation unit should be compiled with `-fno-builtins`.

For builtins that correspond to low-level byte and integer manipulations, an unprefixed inline function must be provided, which contains only a call to the prefixed name.
Only the unprefixed name may be called by users.

The inline function must be defined in a header, and exactly one compilation unit must have a compatible `extern` declaration for that function.
For instance, `uint32_t __builtin_bswap32(uint32_t)` should not be called, instead the following should be implemented:
```c
// in bswap.h (can be included anywhere)
inline uint32_t bswap32(uint32_t x) {
  return __builtin_bswap32(x);
}

// only in bswap.c
#include "bswap.h"
extern uint32_t bswap32(uint32_t x);
```

This ensures changes to add compatibilty for other compilers are less invasive, as we already have a function to include a full implementation within.

## Code Lint

The clang-format tool can check for adherence to this style guide.
The repository contains a `.clang-format` file which configures clang-format according to the rules outlined in this style guide.

You can run clang-format on you changes by calling `git clang-format`.

```sh
cd $REPO_TOP
# make changes to the code ...
git add your_modified_file.c
# format the staged changes
git clang-format
```

To reformat the whole tree the script `util/run-clang-format.sh` can be used.
