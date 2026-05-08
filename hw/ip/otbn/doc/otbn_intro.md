# Introduction to OTBN

OTBN (the **O**pen**T**itan **B**ig **N**umber accelerator) is a specialized coprocessor designed for cryptography.
It runs as part of OpenTitan in addition to the main processor, Ibex.
The OTBN hardware block could also run as part of a different system and interact with a different main processor, but this page will focus on the OpenTitan context.

This page is an introduction and overview of OTBN.
For more detailed information, see the [technical specification](theory_of_operation.md), the [ISA guide](isa.md) and, the [Developer's guide](developers_guide.md).

## How OTBN executes programs

The following diagram illustrates how OTBN and the main processor interact:

![Diagram showing OTBN and Ibex interaction](otbn_operation.svg)

OTBN has its own data and instruction memories, distinct from the memories of the Ibex main processor.
To run an OTBN program, Ibex loads the program into OTBN's instruction memory (and data memory if the program contains stored constants), then writes the input data into the data memory and flips the "execute" bit.
When OTBN is done, it sends an interrupt to Ibex, which reads back the results from data memory.
See the [Developers's guide](developers_guide.md#an-example-program) for an example of a standalone OTBN program.

OTBN protects its data from Ibex in various ways:
- Ibex cannot read OTBN's memory while it is busy executing a program.
- Ibex cannot stop OTBN in the middle of execution; it has to wait until OTBN is done.
- The [key manager][keymgr] can sideload keys directly into OTBN without giving Ibex access to them.
- If OTBN encounters an error, it will lock itself, meaning that Ibex can't read back any data from the program when OTBN is finished (only an error code from a special register).

All together, this mode of interaction keeps OTBN separate enough from Ibex to act as a security boundary.

## Security features

Because OTBN exclusively runs cryptographic algorithms, it is built with extra security features to protect secrets during and after execution.
See the [technical specification](../README.md#security-features) for a full description, but at a high level these features include:
- **no branch prediction or speculative execution**: OTBN stalls for one cycle after jump and branch instructions rather than attempt to predict the next PC, as a mitigation against Spectre-style attacks.
- **no cache**: OTBN's load/store instructions always stall for one cycle, preventing cache-timing attacks.
- **scratchpad memory**: part of OTBN's memory is not accessible by Ibex over the bus, even when OTBN is idle.
- **register blanking**: data paths for unused registers are forced to 0 to avoid leakage via power side-channels.
- **direct access to hardware randomness**: OTBN has a special `RND` register that it can read from to block until entropy is available and then get 256 bits of randomness from a dedicated hardware random-number generator.
- **memory scrambling**: OTBN uses a lightweight cipher to scramble its memories, which helps against data leakage and side-channel attacks.
- **checksum register**: OTBN keeps a register with a checksum of all data written to IMEM and DMEM since the last time the checksum was cleared, which serves as a lightweight write-and-read-back check.
- **instruction count register**: OTBN counts the number of instructions during each program's execution; Ibex can check it as a mitigation against fault-injection attacks that might skip or replay instructions.

Generally speaking, because we expect all the code that runs on OTBN to be sensitive cryptographic routines, the processor does not make tradeoffs for speed over security.
Other aspects of the ISA design allow us to meet our performance requirements despite the speed tradeoffs.

## Instruction set highlights

This section is a quick tour of a few of the more interesting OTBN instructions which enable:

- Efficient big number multiplication using the {{#otbn-insn-ref BN.MULQACC}} instruction.
  The trick is to split bignum multiplications into partial products and accumulate the results using the `ACC` accumulation WSR.
- Modulo addition and subtraction instructions which support single cycle modulo reductions.
  The modulus can be specified with the `MOD` WSR.
- Vectorized (modulo) instructions operating on 32-bit elements inside the 256-bit WDRs ({{#otbn-insn-ref BN.ADDV}}, {{#otbn-insn-ref BN.ADDVM}}, {{#otbn-insn-ref BN.SUBV}}, {{#otbn-insn-ref BN.SUBVM}}, {{#otbn-insn-ref BN.MULV}}).
- A dedicated vectorized Montgomery multiplication instruction {{#otbn-insn-ref BN.MULVM}} especially useful for PQC related computations, in particular for the Number Theoretic Transform (NTT).
- Vectorized instructions to bit-manipulate vectors by shifting each element with {{#otbn-insn-ref BN.SHV}} or reordering the elements with {{#otbn-insn-ref BN.TRN1}} and {{#otbn-insn-ref BN.TRN2}}.
- Hardware loops supporting dynamic and constant number of iterations ({{#otbn-insn-ref LOOP}}, {{#otbn-insn-ref LOOPI}}).
- A 512-bit wide shift with {{#otbn-insn-ref BN.RSHI}} which concatenates two wide registers and then shifts them together.
- Many bignum instructions on OTBN include a shift argument. For example, to compute `w1 + (w2 << 32)`, you can simply write `bn.add   w3, w1, w2 << 32`.

For a full overview of the ISA, see the [ISA guide](isa.md).
See also the [Developers's guide](developers_guide.md) for more detailed guides how to make best use of the ISA.

## Implementation process

At a high level, the process for developing code on OTBN looks something like this:

![OTBN development process diagram](otbn_development_process.svg)

OTBN-simulator tests usually function as a quick check or as unit tests for internal routines, so they are most useful for quick feedback on changes.
Ibex-side tests are more useful for running large or randomized test suites on completed programs, which helps to find bugs in corner cases.
Finally, [SCA analysis](#sca-methodology) can run on either whole programs or small, sensitive subroutines, and helps to determine whether defenses against power and EM side-channels are working.

## Performance

Here are some cycle counts from OTBN programs!
Look below for instructions on how to reproduce these benchmarks.

| Operation | Cycles | Commit | Target | Constant time |
|-----------|-------:|--------|:-------|---------------|
| P256 scalar mult | 670089 | 5bcd7d | p256_scalar_mult_test | yes |
| ECDSA-P256 sign | 704126 | 5bcd7d | p256_ecdsa_sign_test | yes |
| ECDH-P256 verify | 420220 | 5bcd7d | p256_ecdsa_verify_test | no |
| P384 scalar mult | 1632638 | 875b3a | p384_scalar_mult_test | yes |
| ECDSA-P384 sign | 1697985 | 875b3a | p384_ecdsa_sign_test | yes |
| ECDSA-P384 verify | 1075092 | 875b3a | p384_ecdsa_verify_test | no |
| X25519 | 114488 | 636cb7 |  x25519_test1 | yes |
| RSA-2048 modexp (e=65537) | 132028 | 5bcd7d | rsa_2048_enc_test | no |
| RSA-2048 modexp | 18889021 | 5bcd7d | rsa_2048_dec_test | yes |
| RSA-3072 modexp (e=65537)  | 282128 | 5bcd7d | rsa_3072_enc_test | no |
| RSA-3072 modexp  | 61303537 | 5bcd7d | rsa_3072_dec_test | yes |
| RSA-4096 modexp (e=65537)  | 489572 | 5bcd7d | rsa_4096_enc_test | no |
| SHA-256 (2 blocks) | 6851 | 875b3a | sha256_test | yes |
| SHA-512 (1 block) | 3971 | 875b3a | sha512_test | yes |


A few notes:
- Because some OTBN code is still under development, these cycle counts are expected to change a bit as we optimize the code and add hardening countermeasures against fault injection and power/EM side-channel attacks.
- Some of these benchmarks include significant overhead from these countermeasures (for example, we run the inner loop of P-256 scalar multiplication 320 times instead of 256), but in OpenTitan's threat model the price is worthwhile.
- For non-constant-time code, due to the nature of the OTBN benchmarks, it is currently difficult to run multiple tests, so the numbers above reflect only one test each and should be treated as a rough estimate.

### Benchmark reproduction

To reproduce these benchmarks yourself, checkout the specified commit from OpenTitan, then run the OTBN simulator directly on the specified programs.

#### Step 1: Build the tests.

To build the tests with Bazel, run `bazel build //sw/otbn/crypto/tests:<target_name>`, e.g. `bazel build //sw/otbn/crypto/tests:p256_ecdsa_verify_test`.
Then you'll need to find the `.elf` file that Bazel generates; for me this is e.g. `bazel-out/k8-fastbuild-ST-2cc462681f62/bin/sw/otbn/crypto/tests/p256_ecdsa_verify_test.elf`.
You can find the path for yours by running:
```
bazel aquery 'outputs(".*.elf", //sw/otbn/crypto/tests:p256_ecdsa_verify_test)' | grep 'Outputs'
```

Alternatively, you can build the tests manually with `otbn_as.py` and `otbn_ld.py`, as described in the [Developers's  guide](developers_guide.md#toolchain).
In this case you won't need to dig around for the `.elf` file, but you will need to look at `sw/otbn/crypto/tests/BUILD` to see which assembly files need to be included in each target.

#### Step 2: Run the simulator.

Once you have the `.elf` file, either from Bazel or from the manual build process, run `hw/ip/dv/otbnsim/standalone.py --dump-stats - path/to/test.elf` to get a nice printout with the cycle counts plus other statistics.
See the [Developers's guide](developers_guide.md#run-the-iss-instruction-set-simulator) for more information about using the OTBN simulator.

## SCA methodology

Current code for side channel analysis (SCA) on OTBN is in the [sw/device/sca](https://github.com/lowRISC/opentitan/blob/7528f848214589e837ce3b0dacac8385c458b772/sw/device/sca) directory.
The main focus of this code is analysis of power/EM side channels.
For timing side channels, we use [static analysis scripts](#static-checks) instead.

This code runs on Ibex and communicates with scripts from the [ot-sca](https://github.com/lowRISC/ot-sca) repository.
Typically, the SCA code uses a binary entrypoint to the OTBN program that has more degrees of freedom than the one intended for production code.
For example, ECDSA-P256 has the entrypoint [p256_ecdsa](https://github.com/lowRISC/opentitan/blob/7528f848214589e837ce3b0dacac8385c458b772/sw/otbn/crypto/p256_ecdsa.s) for production code, and [p256_ecdsa_sca](https://github.com/lowRISC/opentitan/blob/7528f848214589e837ce3b0dacac8385c458b772/sw/otbn/crypto/p256_ecdsa_sca.s) for side channel analysis.
They call the same underlying library, but the SCA-specific entrypoint allows the caller to select the per-signature secret value `k`, which is always randomly generated in the production-code version.
We can then determine if information about `k` is leaking by trying different known values and seeing if values of `k` that are similar in a certain way have similarities in their traces.
For example, during development we were able to fix a bug in our original implementation that leaked information about the number of leading zeroes in `k`.

## Modeling and formal methods

OTBN is well-suited to modeling because of its relatively simple ISA (52 instructions) and predictable timing behavior.
This means we can easily simulate OTBN's behavior in software and in formal methods tools.

### Machine-readable instruction specifications

OTBN instructions are recorded in [YAML files](https://github.com/lowRISC/opentitan/blob/7528f848214589e837ce3b0dacac8385c458b772/hw/ip/otbn/data/bignum-insns.yml) that include syntax, encoding, and information-flow data.
The OTBN [ISA documentation](isa.md), assembler, simulation tools, and static checkers all read these files.

### OTBN simulator

The OTBN simulator is a Python model of OTBN that is regularly tested against the exact behavior of the SystemVerilog implementation.
Both software and hardware engineers on OpenTitan use it for debugging.
Detailed information on the OTBN simulator can be found in the [Developers's guide](developers_guide.md#run-the-iss-instruction-set-simulator), but the highlights are:
- cycle-by-cycle printouts for instructions and updates to registers/flags/memory
- much faster than simulating OTBN in Verilator

A typical workflow when developing for OTBN is to write both the program itself and a few self-contained tests that can run on the simulator.
If the tests fail, then the cycle-by-cycle printouts help to determine what went wrong.
The simulator is also a good way to get accurate OTBN cycle counts.

You can see the current OTBN simulator tests under [sw/otbn/crypto/tests](https://github.com/lowRISC/opentitan/tree/master/sw/otbn/crypto/tests).

### Formal methods

OTBN is a large part of the reason OpenTitan has a long history of successful formal-methods collaborations.

For example, the OTBN program we use for RSA signature verification in secure boot is [formally verified](https://www.andrew.cmu.edu/user/bparno/papers/galapagos.pdf) in Dafny/Vale.
The authors of the paper created a system called Galápagos, in which a proven-correct low-level implementation can be instantiated for different architectures, including OTBN.
For RSA, they proved that the low-level implementation was equivalent to modular exponentiation, i.e. that it indeed computed `(sig ^ e) mod n`, where `sig` is the signature and `(n, e)` is the RSA public key.
We use their OTBN code in production silicon.
There is no performance hit from the verified code, and since it is burned into hardware ROM it is essential that this code is correct.

We are also pursuing other ongoing collaborations in formal methods, including adding OTBN to the Jasmin compiler.
In the meantime, we occasionally prove small and particularly tricky parts of programs against simplified OTBN models in Coq, such as [here](https://github.com/lowRISC/opentitan/pull/19768).

### Static checks

Building on top of the OTBN simulator, we also have Python tools that model OTBN's control flow and statically:
- [check](https://github.com/lowRISC/opentitan/blob/7528f848214589e837ce3b0dacac8385c458b772/hw/ip/otbn/util/check_const_time.py) if an OTBN program or function is constant-time relative to secrets
- [print](https://github.com/lowRISC/opentitan/blob/7528f848214589e837ce3b0dacac8385c458b772/hw/ip/otbn/util/analyze_information_flow.py) out the information-flow graph for OTBN functions
- [determine](https://github.com/lowRISC/opentitan/blob/7528f848214589e837ce3b0dacac8385c458b772/hw/ip/otbn/util/get_instruction_count_range.py) the minimum and maximum possible instruction count for a program

Some of these have Bazel build integration.
For example, many OTBN functions have a Bazel build target like this that runs the constant-time checker in CI:
```
otbn_consttime_test(
    name = "p256_base_mult_consttime",
    subroutine = "p256_base_mult",
    deps = [
        "//sw/otbn/crypto:p256_ecdsa",
    ],
)
```

## Future Ideas

For future versions of OTBN, we are considering:
- A direct interface from OTBN to the [KMAC][kmac] hardware block, which would allow OTBN to directly run SHA-3 and SHAKE functions
- Expose the [`INSN_CNT`](registers.md#insn_cnt) register to OTBN applications to make cycle count checks at runtime.
  Useful for algorithm which do not execute always in constant time.
- More isolation from Ibex, including potentially giving OTBN its own ROM so that Ibex doesn't need to load secrets into it

[kmac]:  ../../../../hw/ip/kmac/README.md
[keymgr]:  ../../../../hw/ip/keymgr/README.md
