# ML-DSA-87

This directory contains the FIPS-204-compliant and hardened OpenTitan OTBN implementation of the ML-DSA-87 (Dilithium-5) post-quantum cryptography signature algorithm.

The keygen, sign and verify operations are implemented as one OTBN library (`:mldsa87`) and one standalone OTBN app (`:run_mldsa87`).
The implementation is structured hierarchically where the bottom layer consists of routines that operate on polynomials in `Z_q[X] / (X^256 + 1)` composed of 256 24-bit coefficients in the ring Z_q each occupying one 32-bit memory word such that one complete polynomial takes up 1024 bytes.

The polynomial operations form the base for the vector operations through which the lattice is realized.
These vector operations follow the schematics of the three high-level algorithms detailed in FIPS-204.
The general organisation of the ML-DSA OTBN implementation is sketched below.

```
┌─ App/Library ────────────────────────────────────────────────────────────────┐
│                        ╔═════════════════════════════╗                       │
│                        ║        run_mldsa87.s        ║                       │
│                        ║          :mldsa87           ║                       │
│                        ╚══════════════╤══════════════╝                       │
│                                       │                                      │
└───────────────────────────────────────┼──────────────────────────────────────┘
                                        │
┌─ Operations ──────────────────────────┼──────────────────────────────────────┐
│              ┌────────────────────────┼────────────────────────┐             │
│              ▼                        ▼                        ▼             │
│   ╭────────────────────╮   ╭────────────────────╮   ╭────────────────────╮   │
│   │  mldsa87_keygen.s  │   │   mldsa87_sign.s   │   │  mldsa87_verify.s  │   │
│   ╰──────────┬─────────╯   ╰──────────┬─────────╯   ╰──────────┬─────────╯   │
│              │                        │                        │             │
│              └────────────────────────┼────────────────────────┘             │
└───────────────────────────────────────┼──────────────────────────────────────┘
                                        │
┌─ Vector ──────────────────────────────┼──────────────────────────────────────┐
│                                       ▼                                      │
│   ┌──────────────────────────────────────────────────────────────────────┐   │
│   │                            mldsa87_ops.s                             │   │
│   └───────────────────────────────────┬──────────────────────────────────┘   │
│                                       │                                      │
└───────────────────────────────────────┼──────────────────────────────────────┘
                                        │
┌─ Polynomial ──────────────────────────┼──────────────────────────────────────┐
│                                       ▼                                      │
│   ╭────────────────────╮   ╭────────────────────╮   ╭────────────────────╮   │
│   │  mldsa87_arith.s   │   │ mldsa87_encoding.s │   │   mldsa87_ntt.s    │   │
│   ╰────────────────────╯   ╰────────────────────╯   ╰────────────────────╯   │
│   ╭────────────────────╮   ╭────────────────────╮   ╭────────────────────╮   │
│   │  mldsa87_expand.s  │   │  mldsa87_sample.s  │   │ mldsa87_rounding.s │   │
│   ╰────────────────────╯   ╰────────────────────╯   ╰────────────────────╯   │
│               ╭────────────────────╮    ╭────────────────────╮               │
│               │ mldsa87_gadgets.s  │    │  mldsa87_utils.s   │               │
│               ╰────────────────────╯    ╰────────────────────╯               │
│                                                                              │
│               ┄┄┄┄┄┄┄┄┄ imported from sw/otbn/crypto ┄┄┄┄┄┄┄┄┄               │
│               ╭────────────────────╮    ╭────────────────────╮               │
│               │  ../mai_gadgets.s  │    │      ../xof.s      │               │
│               ╰────────────────────╯    ╰────────────────────╯               │
└──────────────────────────────────────────────────────────────────────────────┘

┌─ Memory/Constants ───────────────────────────────────────────────────────────┐
│               ┌────────────────────┐    ┌────────────────────┐               │
│               │   mldsa87_mem.s    │    │    mldsa87.inc     │               │
│               └────────────────────┘    └────────────────────┘               │
└──────────────────────────────────────────────────────────────────────────────┘
```

## Usage

The standalone app `run_mldsa87` reads the operation from the `mldsa87_mode` DMEM word (see the `MLDSA87_MODE_*` constants in `mldsa87.inc`) and calls the corresponding routine.
The keygen and sign routines additionally use the mode to choose between the random and the deterministic (and for sign, the abridged) variants.

Other OTBN apps can depend on the `//sw/otbn/crypto/mldsa87:mldsa87` library and call `mldsa87_keygen`, `mldsa87_sign` and `mldsa87_verify` as subroutines.
Each routine initializes the stack pointer `x31`, the all-zero WDR `w31` and the `MOD` WSR and returns with `ret`.
The caller must not rely on these after the call.
Inputs and outputs are passed through the DMEM buffers declared in `mldsa87_mem.s`.

## Memory Layout

All DMEM buffers are declared at fixed offsets in `mldsa87_mem.s`.
The secret key, public key and signature buffers are shared between the operations, i.e., the output of keygen (`mldsa87_sk_*`, `mldsa87_pk_*`) and sign (`mldsa87_sig_*`) can be consumed by sign and verify without copying.
Dedicated operation buffers (`mldsa87_{keygen,sign,verify}_*`) overlay regions that are not used by the respective operation.
Keygen clobbers the signature, sign clobbers the public key and verify clobbers the secret key.

## Calling Convention

The memory layout governs the implementation choices (e.g., which vectors need to be stored encoded and then decoded on-the-fly when needed) by statically assigning memory regions to intermediate variables as well as input and output data.
This static part of the memory is extended with a dynamic stack onto which a routine can push registers before it starts executing and restore them before returning to the caller routine.
The following rules/conventions are followed in this implementation:

  1. GPR `x31` holds the current address of the stack top.
     This is a global value that must only be modified when pushing and popping registers from the stack.
  2. GPRs `x2-x19` are considered _unclobberable_ registers, meaning that a routine must save their values on the stack before modifying them and restore them before returning.
  3. GPRs `x20-x27` are _clobberable_ registers whose values are not guaranteed to be preserved by a routine.
     These registers are useful for short-lived intermediate data (e.g., to write a CSR) or in portions of the implementation where speed is of the essence and pushing and popping from stack is considered detrimental to the efficiency.
  4. GPRs `x28-x30` and WDRs `w29-w30` are reserved for the global state of the KMAC interface (see preamble of the XOF module).
  5. All WDRs (except `w29-w30` and the all zero `w31`) are considered _clobberable_ and are never preserved, except in the case where they are being used as input/output values of routines (e.g., the MAI routines).
  6. Vector routines do not need to preserve the _unclobberable_ registers as they sit on top of the hierarchy and are not part of other logic except the gluing code of the OTBN apps.
  7. The `MOD` WSR contains three 32-bit constants throughout the computation.
     - `MOD[31:0] = Q = 8380417` (ML-DSA prime number).
     - `MOD[63:32] = MU = -Q^-1 mod 2^32` (Montgomery multiplication constant).
     - `MOD[95:64] = F = 256^-1 * 2^32 * 2^32 mod Q` (Corrective factor of the inverse NTT).

The calling convention of the ML-DSA implementation bears similarities to its x86 counterpart and allows for complex applications that are composed of dozens of interleaved routines with a deep call stack.
The overhead of keeping a dynamic stack is negligible.

## Statistics XXX: to be extended once the implementation reaches maturity.

  - Clock cycles
  - DMEM usage
  - IMEM usage
