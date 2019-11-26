# OpenTitan Freestanding C Headers

This subtree defines headers requred for a C freestanding implementation, as specified in S4p6 of the C11 standard.
Said headers are implemented to the letter as described in respective sections of said standard.

All of `sw/device` is compiled using only these headers, and this directory acts as the sole root against which `#include <...>` directives are resolved.
Headers provided by the system or the compiler are totally inaccessible and should not be used.

These headers are guaranteed to be compatible with processors and compilers implementing the RISC-V ILP32 psABI, though they may be compatible with other architectures and calling conventions on a best-effort basis.
However, compilers *must* be compatible with Clang and GCC's intrinsics.
