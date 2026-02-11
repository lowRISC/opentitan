# ML-DSA-87

This directory contains the FIPS-204-compliant and hardened OpenTitan OTBN implementation of the ML-DSA-87 (Dilithium-5) post-quantum cryptography signature algorithm.

The implementation is structured hierarchically where the bottom layer consists of routines that operate on polynomials in `Z_q[X] / (X^256 + 1)` composed of 256 24-bit coefficients in the ring Z_q each occupying one 32-bit memory word such that one complete polynomial takes up 1024 bytes.

The polynomial operations form the base for the vector operations through which the lattice is realized.
These routines are grouped into three distinct sets (one for each of the fundamental ML-DSA functions; key generation, sign and verify) akin to the three high-level algorithms detailed in FIPS-204.
Every set of vector operation routines then bootstraps one OTBN application that is callable by the host CPU. The general organisation of the ML-DSA OTBN implementation is sketched below.

```
  ML-DSA-87 OTBN Apps
 +--------------------------------------------------------------------------+
 |   +------------------+     +----------------+     +------------------+   |
 |   | mldsa87_keygen.s |     | mldsa87_sign.s |     | mldsa87_verify.s |   |
 |   +--------+---------+     +--------+-------+     +---------+--------+   |
 +------------|------------------------|-----------------------|------------+
              |                        |                       |
              |                        |                       |
  Vector Ops  |                        |                       |
 +------------|------------------------|-----------------------|------------+
 | +----------+-----------+ +----------+---------+ +-----------+----------+ |
 | | mldsa87_keygen_ops.s | | mldsa87_sign_ops.s | | mldsa87_verify_ops.s | |
 | +----------------------+ +--------------------+ +----------------------+ |
 +-------------------------------------+------------------------------------+
                                       |
                                       |
  Polynomial Ops                       |
 +-------------------------------------+------------------------------------+
 | +-----------------+       +--------------------+    +------------------+ |
 | | mldsa87_arith.s |       | mldsa87_encoding.s |    | mldsa87_expand.s | |
 | +-----------------+       +--------------------+    +------------------+ |
 | +-------------------+     +----------------+        +------------------+ |
 | | mldsa87_gadgets.s |     | mldsa87_norm.s |        | mldsa87_reduce.s | |
 | +-------------------+     +----------------+        +------------------+ |
 | +--------------------+    +------------------+      +---------------+    |
 | | mldsa87_rounding.s |    | mldsa87_sample.s |      | mldsa87_xof.s |    |
 | +--------------------+    +------------------+      +---------------+    |
 +--------------------------------------------------------------------------+
```

## Calling Convention

Each of the three ML-DSA apps can be compiled holistically as a single binary with a corresponding memory file (not depicted in the diagram).
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

The calling convention of the ML-DSA implementation bears similarities to its x86 counterpart and allows for complex applications that are composed of dozens of interleaved routines with a deep call stack.
The overhead of keeping a dynamic stack is negligible.

## Statistics XXX: to be extended once the implementation reaches maturity.

  - Clock cycles
  - DMEM usage
  - IMEM usage
