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

<!-- To render a backtick in inline code in markdown, you need to double the surrounding backticks.
https://daringfireball.net/projects/markdown/syntax#code -->
***Variables mentioned in comments should be delimited with backtick (`` ` ``) characters.***

Example:

```c
// `ptr` can never be NULL for reasons.
```

Note also [Public function (API) documentation](#public-function-api-documentation) below.

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

### Linker Script- and Assembly-Provided Symbols

Some C/C++ programs may need to use symbols that are defined by a linker script or in an external assembly file.
Referring to linker script- and assembly-provided symbols can be complex and error-prone, as they don't quite work like C's global variables.
We have chosen the following approach based on the examples in [the binutils ld manual](https://sourceware.org/binutils/docs/ld/Source-Code-Reference.html).

If you need to refer to the symbol `_my_linker_symbol`, the correct way to do so is with an incomplete extern char array declaration, as shown below.
It is good practice to provide a comment that directs others to where the symbol is actually defined, and whether the symbol should be treated as a memory address or another kind of value.
```c
/**
 * `_my_linker_symbol` is defined in the linker script `sw/device/my_feature.ld`.
 *
 * `_my_linker_symbol` is a memory address in RAM.
 */
extern char _my_linker_symbol[];
```

A symbol's value is exposed using its address, and declaring it this way allows you to use the symbol where you need a pointer.
```c
char my_buffer[4];
memcpy(my_buffer, _my_linker_symbol, sizeof(my_buffer));
```

If the symbol has been defined to a non-address value (usually using `ABSOLUTE()` in a linker script, or `.set` in assembly), you must cast the symbol to obtain its value using `(intptr_t)_my_linker_symbol`.
You must not dereference a symbol that has non-address value.

### Public function (API) documentation

***It is recommended to document public functions, classes, methods, and data structures in the header file with a Doxygen-style comment.***

The first line of the comment is the summary, followed by a new line, and an optional longer description.
Input arguments and return arguments can be documented with `@param` and `@return` if they are not self-explanatory from the name.

The documentation tool will also render markdown within descriptions, so backticks should be used to get monospaced text.
It can also generate references to other named declarations using `#other_function` (for C-style declarations), or `ns::foo` (for C++ declarations).

Example:

```c
/**
 * Do something amazing
 *
 * Create a rainbow and place a unicorn at the bottom of it. `pots_of_gold`
 * pots of gold will be positioned on the east end of the rainbow.
 *
 * Can be recycled with #recycle_rainbow.
 *
 * @param pots_of_gold Number of gold pots to place next to the rainbow
 * @param unicorns Number of unicorns to position on the rainbow
 * @return 0 if the function was successful, -1 otherwise
 */
int create_rainbow(int pots_of_gold, int unicorns);
```

### Polyglot headers

***Headers intended to be included from both languages must contain `extern` guards; `#include`s should not be wrapped in `extern "C" {}`.***

A *polyglot header* is a header file that can be safely included in either a `.c` or `.cc` file.
In particular, this means that the file must not depend on any of the places where C and C++ semantics disagree.
For example:
- `sizeof(struct {})` and `sizeof(true)` are different in C and C++.
- Function-scope `static` variables generate lock calls in C++.
- Some libc macros, like `static_assert`, may not be present in C++.
- Character literals type as `char` in C++ but `int` in C.

Such files must be explictly marked with `extern` guards like the following, starting after the file's `#include`s.
```
#ifdef __cplusplus
extern "C" {
#endif

// Declarations...

#ifdef __cplusplus
}  // extern "C"
#endif
```
Moreover, all non-system `#includes` in a polyglot header must also be of other polyglot headers.
(In other words, all C system headers may be assumed to be polyglot, even if they lack guards.)

Additionally, it is forbidden to wrap `#include` statements in `extern "C"` in a C++ file.
While this does correctly set the ABI for a header implemented in C, that header may contain code that subtly depends on the peculiarities of C.

This last rule is waived for third-party headers, which may be polyglot but not declared in our style.

### X Macros

In order to avoid repetitive definitions or statements, we allow the use of [X Macros](https://en.wikipedia.org/wiki/X_Macro) in our C and C++ code.

Uses of X Macros should follow the following example, which uses this pattern in a switch definition:
```c
int get_field2(int identifier) {
  switch (identifier) {
#define ITEM(id_field, data_field1, data_field2) \
    case id_field:                               \
      return data_field2;
#include "path/to/item.def"
    default:
      return 0;
  }
}
```
This example expands to a case statement for each item, which returns the `data_field2` value where the passed in identifier matches `id_field`.

The contents of the X Macro file from this example ("path/to/item.def") should look like:
```c

/**
 * \def ITEM(id_field, data_field1, data_field2)
 *
 * <Documentation about meaning of ITEM fields>
 */
#ifndef ITEM
#error ITEM(id_field, data_field1, data_field2) must be defined
#endif

ITEM(fields...)
ITEM(fields...)

#undef ITEM
```

These X Macro files must:

*   Have the extension `.def`.
    The file's basename should match the X Macro name.
    This is so we can easily identify that this is an X Macro, which will be used by the preprocessor, and is required at compile-time.
*   Document the X Macro and the meaning of its fields.
*   Error if the X Macro is not defined.
*   Include a sequence of X Macro uses, one per line, omitting following semicolons.
    Omitting semicolons allows X Macros to be used in either expression or statement position, which is useful.
*   Undefine the X Macro name at the end of the file.

X Macro field values should be valid C constant literals.
The first field of an X Macro should be the primary identifier, as shown in the example.

X Macros should be kept as simple as possible.
X Macro files should endeavour to only define one kind of X Macro, and separate files should be used for other X Macros.
If possible, X Macros should only be used in implementation files, and should be avoided in headers.

The code using an X Macro must:

*   Define the X Macro name, including any separators (such as semicolons or commas) within the definition.
    It is usually clearer if you split the definition over multiple lines.
*   Immediately after the definition, include the `.def` file for the X Macro.



## C++ Style Guide {#cxx-style-guide}

### C++ Version {#cxx-version}

C++ code should target C++14.

### Aggregate Initializers

***C++20-style designated initializers are permitted in C++ code, when used with POD types.***

While we target C++14, both GCC and Clang allow C++20 designated initializers in C++14-mode, as an extension:
```
struct Foo { int a, b; };

Foo f = { .a = 1, .b = 42, };
```

This feature is fairly mature in both compilers, though it varies from the C11 variant in two ways important ways:
  - It can only be used with structs and unions, not arrays.
  - Members must be initialized in declaration order.

Because it is especially useful with types declared for C, we allow designatued initializers whenever the type is a plain-old-data type, and:
  - All members are public.
  - It has no non-trivial constructors.
  - It has no `virtual` members.

Furthermore, designated initializers do not play well with type deduction and overload resolution.
As such, they are forbidden in the following contexts:
- Do not call overloaded functions with a designated initializer: `overloaded({ .foo = 0 })`.
  Instead, disambiguate with syntax like `T var = { .foo = 0 }; overloaded(var);`.
- Do not use designated initializers in any place where they would be used for type defuction.
  This includes `auto`, such as `auto var = { .foo = 0 };`, and a templated argument in a template function.

It is recommended to only use designated initializers with types which use C-style declarations.

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

***All symbols in a particular header must share the same unique prefix.***

"Prefix" in this case refers to the identifying string of words, and not the specific type/struct/enum/constant/macro-based capitalisation.
This rule also deviates from the Google C++ style guide, because C does not have namespaces, so we have to use long names to avoid name clashes.
Symbols that have specific, global meaning imparted by an external script or specification may break this rule.
For example:
```c
// in my_unit.h
extern const int kMyUnitMaskValue = 0xFF;

typedef enum { kMyUnitReturnOk } my_unit_return_t;

my_unit_return_t my_unit_init(void);
```

***The names of enumeration constants must be prefixed with the name of their respective enumeration type.***

Again, this is because C does not have namespaces.
The exact capitalisation does not need to match, as enumeration type names have a different capitalisation rule to enumeration constants.
For example:
```c
typedef enum my_wonderful_option {
  kMyWonderfulOptionEnabled,
  kMyWonderfulOptionDisabled,
  kMyWonderfulOptionOnlySometimes
} my_wonderful_option_t;
```

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

When initializing an array, initializers *may* be designated when that makes the array more readable (e.g., lookup tables that are mostly zeroed).
Mixing designated and undesignated initializers, or using nested initializers, is still forbidden.

### Function Declarations

***All function declarations in C must include a list of the function's parameters, with their types.***

C functions declared as `return_t my_function()` are called "K&R declarations", and are type compatible with any list of arguments, with any types.
Declarations of this type allow type confusion, especially if the function definition is not available.

The correct way to denote that a function takes no arguments is using the parameter type `void`.
For example `return_t my_function(void)` is the correct way to declare that `my_function` takes no arguments.

The parameter names in every declaration should match the parameter names in the function definition.

### Inline Functions

Functions that we strongly wish to be inlined, and which are part of a public interface, should be declared as an inline function.
This annotation serves as an indication to the programmer that the function has a low calling overhead, despite being part of a public interface.
Presence---or lack---of an `inline` annotation does not imply a function will---or will not---be inlined by the compiler.

[C11](#c-version) standardised inline functions, learning from the mistakes in C++ and various nonstandard extensions.
This means there are many legacy ways to define an inline function in C.
We have chosen to follow how C11 designed the `inline` keyword.

The function definition is written in a header file, with the keyword `inline`:
```c
// in my_inline.h
inline int my_inline_function(long param1) {
  // implementation
}
```

There should be exactly one compilation unit with a compatible `extern` declaration of the same function:
```c
// in my_inline.c
#include <my_inline.h>
extern int my_inline_function(long param1);
```

Any compilation unit that includes `my_inline.h` must be linked to the compilation unit with the extern declarations.
This ensures that if the compiler chooses not to inline `my_inline_function`, there is a function definition that can be called.
This also ensures that the function can be used via a function pointer.

### Static Declarations

Declarations marked `static` must not appear in header files.
Header files are declarations of public interfaces, and `static` definitions are copied, not shared, between compilation units.

This is especially important in the case of a polyglot header, since function-local static declarations have different, incompatible semantics in C and C++.

Functions marked `static` must not be marked `inline`.
The compiler is capable of inlining static functions without the `inline` annotation.

### Nonstandard Attributes

The following nonstandard attributes may be used:
*   `section(<name>)` to put a definition into a given object section.
*   `weak` to make a symbol definition have weak linkage.
*   `interrupt` to ensure a function has the right prolog and epilog for interrupts (this involves saving and restoring more registers than normal).
*   `packed` to ensure a struct contains no padding.
*   `warn_unused_result`, to mark functions that return error values that should be checked.

It is recommended that other nonstandard attributes are not used, especially where C11 provides a standard means to accomplish the same thing.

All nonstandard attributes must be supported by both GCC and Clang.

Nonstandard attributes must be written before the declaration, like the following example, so they work with both declarations and definitions.

```c
__attribute__((section(".crt"))) void _crt(void);
```

### Nonstandard Compiler Builtins

In order to avoid a total reliance on one single compiler, any nonstandard compiler builtins (also known as intrinsics) should be used via a single canonical definition.
This ensures changes to add compatibilty for other compilers are less invasive, as we already have a function to include a full implementation within.

All nonstandard builtins should be supported by both GCC and Clang.
Compiler builtin usage is complex, and it is recommended that a compiler engineer reviews any code that adds new builtins.

In the following, `__builtin_foo` is the *builtin name* and `foo` is the corresponding *general name*.

***The use of nonstandard compiler builtins must be hidden using a canonical, compatible definition.***

There are two ways of providing this canonical definition, depending on what the builtin does.

For builtins that correspond to a C library function, the general name must be available to the linker, as the compiler may still insert a call to this function.
Unfortunately, older versions of GCC do not support the `__has_builtin()` preprocessor function, so compiler detection of support for these builtins is next to impossible.
In this case, a standards-compliant implementation of the general name must be provided, and the compilation unit should be compiled with `-fno-builtins`.

For builtins that correspond to low-level byte and integer manipulations, an [inline function](#inline-functions) should be provided with a general name, which contains a call to the builtin name itself, or an equivalent implementation.
Only the general name may be called by users: for instance, `uint32_t __builtin_bswap32(uint32_t)` must not be called, instead users should use `inline uint32_t bswap32(uint32_t x)`.
Where the general name is already taken by an incompatible host or device library symbol, the general name can be prefixed with the current C namespace prefix, for instance `inline uint32_t bitfield_bswap32(uint32_t x)` for a function in `bitfield.h`.
Where the general name is a short acronym, the name may be expanded for clarity, for instance `__builtin_ffs` may have a canonical definition named `bitfield_find_first_set`.
Where there are compatible typedefs that convey additional meaning (e.g. `uint32_t` vs `unsigned int`), these may be written instead of the official builtin types.

For builtins that cannot be used via a compatible function definition (e.g. if an argument is a type or identifier), there should be a single canonical preprocessor definition with the general name, which expands to the builtin.

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
