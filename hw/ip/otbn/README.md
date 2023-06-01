# OpenTitan Big Number Accelerator (OTBN) Technical Specification

{{#block-dashboard otbn}}

# Overview

This document specifies functionality of the OpenTitan Big Number Accelerator, or OTBN.
OTBN is a coprocessor for asymmetric cryptographic operations like RSA or Elliptic Curve Cryptography (ECC).

This module conforms to the [Comportable guideline for peripheral functionality](../../../doc/contributing/hw/comportability/README.md).
See that document for integration overview within the broader top level system.

## Features

* Processor optimized for wide integer arithmetic
* 32b wide control path with 32 32b wide registers
* 256b wide data path with 32 256b wide registers
* Full control-flow support with conditional branch and unconditional jump instructions, hardware loops, and hardware-managed call/return stacks.
* Reduced, security-focused instruction set architecture for easier verification and the prevention of data leaks.
* Built-in access to random numbers.

## Description

OTBN is a processor, specialized for the execution of security-sensitive asymmetric (public-key) cryptography code, such as RSA or ECC.
Such algorithms are dominated by wide integer arithmetic, which are supported by OTBN's 256b wide data path, registers, and instructions which operate these wide data words.
On the other hand, the control flow is clearly separated from the data, and reduced to a minimum to avoid data leakage.

The data OTBN processes is security-sensitive, and the processor design centers around that.
The design is kept as simple as possible to reduce the attack surface and aid verification and testing.
For example, no interrupts or exceptions are included in the design, and all instructions are designed to be executable within a single cycle.

OTBN is designed as a self-contained co-processor with its own instruction and data memory, which is accessible as a bus device.

## Compatibility

OTBN is not designed to be compatible with other cryptographic accelerators.
It received some inspiration from assembly code available from the [Chromium EC project](https://chromium.googlesource.com/chromiumos/platform/ec/),
which has been formally verified within the [Fiat Crypto project](http://adam.chlipala.net/papers/FiatCryptoSP19/FiatCryptoSP19.pdf).

# Instruction Set

OTBN is a processor with a custom instruction set.
The full ISA description can be found in our [ISA manual](./doc/isa.md).
The instruction set is split into two groups:

* The **base instruction subset** operates on the 32b General Purpose Registers (GPRs).
  Its instructions are used for the control flow of a OTBN application.
  The base instructions are inspired by RISC-V's RV32I instruction set, but not compatible with it.
* The **big number instruction subset** operates on 256b Wide Data Registers (WDRs).
  Its instructions are used for data processing.

## Processor State

### General Purpose Registers (GPRs)

OTBN has 32 General Purpose Registers (GPRs), each of which is 32b wide.
The GPRs are defined in line with RV32I and are mainly used for control flow.
They are accessed through the base instruction subset.
GPRs aren't used by the main data path; this operates on the [Wide Data Registers](#wide-data-registers-wdrs), a separate register file, controlled by the big number instructions.

<table>
  <tr>
    <td><code>x0</code></td>
    <td>Zero register. Reads as 0; writes are ignored.</td>
  </tr>
  <tr>
    <td><code>x1</code></td>
<td>

Access to the [call stack](#call-stack)

</td>
  </tr>
  <tr>
    <td><code>x2</code> ... <code>x31</code></td>
    <td>General purpose registers</td>
  </tr>
</table>

Note: Currently, OTBN has no "standard calling convention," and GPRs other than `x0` and `x1` can be used for any purpose.
If a calling convention is needed at some point, it is expected to be aligned with the RISC-V standard calling conventions, and the roles assigned to registers in that convention.
Even without a agreed-on calling convention, software authors are encouraged to follow the RISC-V calling convention where it makes sense.
For example, good choices for temporary registers are `x6`, `x7`, `x28`, `x29`, `x30`, and `x31`.

### Call Stack

OTBN has an in-built call stack which is accessed through the `x1` GPR.
This is intended to be used as a return address stack, containing return addresses for the current stack of function calls.
See the documentation for {{#otbn-insn-ref JAL}} and {{#otbn-insn-ref JALR}} for a description of how to use it for this purpose.

The call stack has a maximum depth of 8 elements.
Each instruction that reads from `x1` pops a single element from the stack.
Each instruction that writes to `x1` pushes a single element onto the stack.
An instruction that reads from an empty stack or writes to a full stack causes a `CALL_STACK` [software error](#design-details-errors).

A single instruction can both read and write to the stack.
In this case, the read is ordered before the write.
Providing the stack has at least one element, this is allowed, even if the stack is full.

### Control and Status Registers (CSRs)

Control and Status Registers (CSRs) are 32b wide registers used for "special" purposes, as detailed in their description;
they are not related to the GPRs.
CSRs can be accessed through dedicated instructions, {{#otbn-insn-ref CSRRS}} and {{#otbn-insn-ref CSRRW}}.
Writes to read-only (RO) registers are ignored; they do not signal an error.
All read-write (RW) CSRs are set to 0 when OTBN starts an operation (when 1 is written to [`CMD.start`](data/otbn.hjson#cmd)).

<!-- This list of CSRs is replicated in otbn_env_cov.sv, wsr.py, the
     RTL and in rig/model.py. If editing one, edit the other four as well. -->
<table>
  <thead>
    <tr>
      <th>Number</th>
      <th>Access</th>
      <th>Name</th>
      <th>Description</th>
    </tr>
  </thead>
  <tbody>
    <tr>
      <td>0x7C0</td>
      <td>RW</td>
      <td>FG0</td>
      <td>
        Wide arithmetic flag group 0.
        This CSR provides access to flag group 0 used by wide integer arithmetic.
        <strong>FLAGS</strong>, <strong>FG0</strong> and <strong>FG1</strong> provide different views on the same underlying bits.
        <table>
          <thead>
            <tr><th>Bit</th><th>Description</th></tr>
          </thead>
          <tbody>
            <tr><td>0</td><td>Carry of Flag Group 0</td></tr>
            <tr><td>1</td><td>MSb of Flag Group 0</td></tr>
            <tr><td>2</td><td>LSb of Flag Group 0</td></tr>
            <tr><td>3</td><td>Zero of Flag Group 0</td></tr>
          </tbody>
        </table>
      </td>
    </tr>
    <tr>
      <td>0x7C1</td>
      <td>RW</td>
      <td>FG1</td>
      <td>
        Wide arithmetic flag group 1.
        This CSR provides access to flag group 1 used by wide integer arithmetic.
        <strong>FLAGS</strong>, <strong>FG0</strong> and <strong>FG1</strong> provide different views on the same underlying bits.
        <table>
          <thead>
            <tr><th>Bit</th><th>Description</th></tr>
          </thead>
          <tbody>
            <tr><td>0</td><td>Carry of Flag Group 1</td></tr>
            <tr><td>1</td><td>MSb of Flag Group 1</td></tr>
            <tr><td>2</td><td>LSb of Flag Group 1</td></tr>
            <tr><td>3</td><td>Zero of Flag Group 1</td></tr>
          </tbody>
        </table>
      </td>
    </tr>
    <tr>
      <td>0x7C8</td>
      <td>RW</td>
      <td>FLAGS</td>
      <td>
        Wide arithmetic flag groups.
        This CSR provides access to both flags groups used by wide integer arithmetic.
        <strong>FLAGS</strong>, <strong>FG0</strong> and <strong>FG1</strong> provide different views on the same underlying bits.
        <table>
          <thead>
            <tr><th>Bit</th><th>Description</th></tr>
          </thead>
          <tbody>
            <tr><td>0</td><td>Carry of Flag Group 0</td></tr>
            <tr><td>1</td><td>MSb of Flag Group 0</td></tr>
            <tr><td>2</td><td>LSb of Flag Group 0</td></tr>
            <tr><td>3</td><td>Zero of Flag Group 0</td></tr>
            <tr><td>4</td><td>Carry of Flag Group 1</td></tr>
            <tr><td>5</td><td>MSb of Flag Group 1</td></tr>
            <tr><td>6</td><td>LSb of Flag Group 1</td></tr>
            <tr><td>7</td><td>Zero of Flag Group 1</td></tr>
          </tbody>
        </table>
      </td>
    </tr>
    <tr>
      <td>0x7D0</td>
      <td>RW</td>
      <td>MOD0</td>
      <td>
        Bits [31:0] of the modulus operand, used in the {{#otbn-insn-ref BN.ADDM}}/{{#otbn-insn-ref BN.SUBM}} instructions.
        This CSR is mapped to the MOD WSR.
      </td>
    </tr>
    <tr>
      <td>0x7D1</td>
      <td>RW</td>
      <td>MOD1</td>
      <td>
        Bits [63:32] of the modulus operand, used in the {{#otbn-insn-ref BN.ADDM}}/{{#otbn-insn-ref BN.SUBM}} instructions.
        This CSR is mapped to the MOD WSR.
      </td>
    </tr>
    <tr>
      <td>0x7D2</td>
      <td>RW</td>
      <td>MOD2</td>
      <td>
        Bits [95:64] of the modulus operand, used in the {{#otbn-insn-ref BN.ADDM}}/{{#otbn-insn-ref BN.SUBM}} instructions.
        This CSR is mapped to the MOD WSR.
      </td>
    </tr>
    <tr>
      <td>0x7D3</td>
      <td>RW</td>
      <td>MOD3</td>
      <td>
        Bits [127:96] of the modulus operand, used in the {{#otbn-insn-ref BN.ADDM}}/{{#otbn-insn-ref BN.SUBM}} instructions.
        This CSR is mapped to the MOD WSR.
      </td>
    </tr>
    <tr>
      <td>0x7D4</td>
      <td>RW</td>
      <td>MOD4</td>
      <td>
        Bits [159:128] of the modulus operand, used in the {{#otbn-insn-ref BN.ADDM}}/{{#otbn-insn-ref BN.SUBM}} instructions.
        This CSR is mapped to the MOD WSR.
      </td>
    </tr>
    <tr>
      <td>0x7D5</td>
      <td>RW</td>
      <td>MOD5</td>
      <td>
        Bits [191:160] of the modulus operand, used in the {{#otbn-insn-ref BN.ADDM}}/{{#otbn-insn-ref BN.SUBM}} instructions.
        This CSR is mapped to the MOD WSR.
      </td>
    </tr>
    <tr>
      <td>0x7D6</td>
      <td>RW</td>
      <td>MOD6</td>
      <td>
        Bits [223:192] of the modulus operand, used in the {{#otbn-insn-ref BN.ADDM}}/{{#otbn-insn-ref BN.SUBM}} instructions.
        This CSR is mapped to the MOD WSR.
      </td>
    </tr>
    <tr>
      <td>0x7D7</td>
      <td>RW</td>
      <td>MOD7</td>
      <td>
        Bits [255:224] of the modulus operand, used in the {{#otbn-insn-ref BN.ADDM}}/{{#otbn-insn-ref BN.SUBM}} instructions.
        This CSR is mapped to the MOD WSR.
      </td>
    </tr>
    <tr>
      <td>0x7D8</td>
      <td>RW</td>
      <td>RND_PREFETCH</td>
      <td>
        Write to this CSR to begin a request to fill the RND cache.
        Always reads as 0.
      </td>
    </tr>
    <tr>
      <td>0xFC0</td>
      <td>RO</td>
      <td>RND</td>
      <td>
An AIS31-compliant class PTG.3 random number with guaranteed entropy and forward and backward secrecy.
Primarily intended to be used for key generation.

The number is sourced from the EDN via a single-entry cache.
Reads when the cache is empty will cause OTBN to be stalled until a new random number is fetched from the EDN.
      </td>
    </tr>
    <tr>
      <td>0xFC1</td>
      <td>RO</td>
      <td>URND</td>
      <td>
A random number without guaranteed secrecy properties or specific statistical properties.
Intended for use in masking and blinding schemes.
Use RND for high-quality randomness.

The number is sourced from an local PRNG.
Reads never stall.
      </td>
    </tr>
  </tbody>
</table>

### Wide Data Registers (WDRs)

In addition to the 32b wide GPRs, OTBN has a second "wide" register file, which is used by the big number instruction subset.
This register file consists of NWDR = 32 Wide Data Registers (WDRs).
Each WDR is WLEN = 256b wide.

Wide Data Registers (WDRs) and the 32b General Purpose Registers (GPRs) are separate register files.
They are only accessible through their respective instruction subset:
GPRs are accessible from the base instruction subset, and WDRs are accessible from the big number instruction subset (`BN` instructions).

| Register |
|----------|
| w0       |
| w1       |
| ...      |
| w31      |

### Wide Special Purpose Registers (WSRs)

OTBN has 256b Wide Special purpose Registers (WSRs).
These are analogous to the 32b CSRs, but are used by big number instructions.
They can be accessed with the {{#otbn-insn-ref BN.WSRR}} and {{#otbn-insn-ref BN.WSRW}} instructions.
Writes to read-only (RO) registers are ignored; they do not signal an error.
All read-write (RW) WSRs are set to 0 when OTBN starts an operation (when 1 is written to [`CMD.start`](data/otbn.hjson#cmd)).

<!-- This list of WSRs is replicated in otbn_env_cov.sv, wsr.py, the
     RTL and in rig/model.py. If editing one, edit the other four as well. -->
<table>
  <thead>
    <tr>
      <th>Number</th>
      <th>Access</th>
      <th>Name</th>
      <th>Description</th>
    </tr>
  </thead>
  <tbody>
    <tr>
      <td>0x0</td>
      <td>RW</td>
      <td>MOD</td>
<td>

The modulus used by the {{#otbn-insn-ref BN.ADDM}} and {{#otbn-insn-ref BN.SUBM}} instructions.
This WSR is also visible as CSRs `MOD0` through to `MOD7`.

</td>
    </tr>
    <tr>
      <td>0x1</td>
      <td>RO</td>
      <td>RND</td>
      <td>
An AIS31-compliant class PTG.3 random number with guaranteed entropy and forward and backward secrecy.
Primarily intended to be used for key generation.

The number is sourced from the EDN via a single-entry cache.
Reads when the cache is empty will cause OTBN to be stalled until a new random number is fetched from the EDN.
      </td>
    </tr>
    <tr>
      <td>0x2</td>
      <td>RO</td>
      <td>URND</td>
      <td>
A random number without guaranteed secrecy properties or specific statistical properties.
Intended for use in masking and blinding schemes.
Use RND for high-quality randomness.

The number is sourced from a local PRNG.
Reads never stall.
      </td>
    </tr>
    <tr>
      <td>0x3</td>
      <td>RW</td>
      <td>ACC</td>
      <td>
        The accumulator register used by the {{#otbn-insn-ref BN.MULQACC}} instruction.
      </td>
    </tr>
    <tr>
      <td>0x4</td>
      <td>RO</td>
      <td><a name="key-s0-l">KEY_S0_L</a></td>
      <td>
Bits [255:0] of share 0 of the 384b OTBN sideload key provided by the [Key Manager](../keymgr/README.md).

A `KEY_INVALID` software error is raised on read if the Key Manager has not provided a key.
      </td>
    </tr>
    <tr>
      <td>0x5</td>
      <td>RO</td>
      <td><a name="key-s0-h">KEY_S0_H</a></td>
      <td>
Bits [255:128] of this register are always zero.
Bits [127:0] contain bits [383:256] of share 0 of the 384b OTBN sideload key provided by the [Key Manager](../keymgr/README.md).

A `KEY_INVALID` software error is raised on read if the Key Manager has not provided a valid key.
      </td>
    </tr>
    <tr>
      <td>0x6</td>
      <td>RO</td>
      <td><a name="key-s1-l">KEY_S1_L</a></td>
      <td>
Bits [255:0] of share 1 of the 384b OTBN sideload key provided by the [Key Manager](../keymgr/README.md).

A `KEY_INVALID` software error is raised on read if the Key Manager has not provided a valid key.
      </td>
    </tr>
    <tr>
      <td>0x7</td>
      <td>RO</td>
      <td><a name="key-s1-h">KEY_S1_H</a></td>
      <td>
Bits [255:128] of this register are always zero.
Bits [127:0] contain bits [383:256] of share 1 of the 384b OTBN sideload key provided by the [Key Manager](../keymgr/README.md).

A `KEY_INVALID` software error is raised on read if the Key Manager has not provided a valid key.
      </td>
    </tr>
  </tbody>
</table>

### Flags

In addition to the wide register file, OTBN maintains global state in two groups of flags for the use by wide integer operations.
Flag groups are named Flag Group 0 (`FG0`), and Flag Group 1 (`FG1`).
Each group consists of four flags.
Each flag is a single bit.

- `C` (Carry flag).
  Set to 1 an overflow occurred in the last arithmetic instruction.

- `M` (MSb flag)
  The most significant bit of the result of the last arithmetic or shift instruction.

- `L` (LSb flag).
  The least significant bit of the result of the last arithmetic or shift instruction.

- `Z` (Zero Flag)
  Set to 1 if the result of the last operation was zero; otherwise 0.

The `M`, `L`, and `Z` flags are determined based on the result of the operation as it is written back into the result register, without considering the overflow bit.

### Loop Stack

OTBN has two instructions for hardware-assisted loops: {{#otbn-insn-ref LOOP}} and {{#otbn-insn-ref LOOPI}}.
Both use the same state for tracking control flow.
This is a stack of tuples containing a loop count, start address and end address.
The stack has a maximum depth of eight and the top of the stack is the current loop.

# Security Features

OTBN is a security co-processor.
It contains various security features and is hardened against side-channel analysis and fault injection attacks.
The following sections describe the high-level security features of OTBN.
Refer to the [Design Details](#design-details) section for a more in-depth description.

## Data Integrity Protection

OTBN's data integrity protection is designed to protect the data stored and processed within OTBN from modifications through physical attacks.

Data in OTBN travels along a data path which includes the data memory (DMEM), the load-store-unit (LSU), the register files (GPR and WDR), and the execution units.
Whenever possible, data transmitted or stored within OTBN is protected with an integrity protection code which guarantees the detection of at least three modified bits per 32 bit word.
Additionally, instructions and data stored in the instruction and data memory, respectively, are scrambled with a lightweight, non-cryptographically-secure cipher.

Refer to the [Data Integrity Protection](./doc/theory_of_operation.md#data-integrity-protection) section for details of how the data integrity protections are implemented.

## Secure Wipe

OTBN provides a mechanism to securely wipe all state it stores, including the instruction memory.

The full secure wipe mechanism is split into three parts:
- [Data memory secure wipe](./doc/theory_of_operation.md#data-memory-dmem-secure-wipe)
- [Instruction memory secure wipe](./doc/theory_of_operation.md#instruction-memory-imem-secure-wipe)
- [Internal state secure wipe](./doc/theory_of_operation.md#internal-state-secure-wipe)

A secure wipe is performed automatically in certain situations, or can be requested manually by the host software.
The full secure wipe is automatically initiated as a local reaction to a fatal error.
In addition, it can be triggered by the [Life Cycle Controller](../lc_ctrl/README.md) before RMA entry using the `lc_rma_req/ack` interface.
In both cases OTBN enters the locked state afterwards and needs to be reset.
A secure wipe of only the internal state is performed after reset, whenever an OTBN operation is complete, and after a recoverable error.
Finally, host software can manually trigger the data memory and instruction memory secure wipe operations by issuing an appropriate
[command](./doc/theory_of_operation.md#operations-and-commands).

Refer to the [Secure Wipe](./doc/theory_of_operation.md#secure-wipe) section for implementation details.

## Instruction Counter

In order to detect and mitigate fault injection attacks on the OTBN, the host CPU can read the number of executed instructions from [`INSN_CNT`](data/otbn.hjson#insn_cnt) and verify whether it matches the expectation.
The host CPU can clear the instruction counter when OTBN is not running.
Writing any value to [`INSN_CNT`](data/otbn.hjson#insn_cnt) clears this register to zero.
Write attempts while OTBN is running are ignored.

## Key Sideloading

OTBN software can make use of a single 384b wide key provided by the [Key Manager](../keymgr/README.md), which is made available in two shares.
The key is passed through a dedicated connection between the Key Manager and OTBN to avoid exposing it to other components.
Software can access the first share of the key through the [`KEY_S0_L`](#key-s0-l) and [`KEY_S0_H`](#key-s0-h) WSRs, and the second share of the key through the [`KEY_S1_L`](#key-s1-l) and [`KEY_S1_H`](#key-s1-h) WSRs.

It is up to host software to configure the Key Manager so that it provides the right key to OTBN at the start of the operation, and to remove the key again once the operation on OTBN has completed.
A `KEY_INVALID` software error is raised if OTBN software accesses any of the `KEY_*` WSRs when the Key Manager has not presented a key.

## Blanking

To reduce side channel leakage OTBN employs a blanking technique on certain control and data paths.
When a path is blanked it is forced to 0 (by ANDing the path with a blanking signal) preventing sensitive data bits producing a power signature via that path where that path isn't needed for the current instruction.

Blanking controls all come directly from flops to prevent glitches in decode logic reducing the effectiveness of the blanking.
These control signals are determined in the [prefetch stage](#instruction-prefetch) via pre-decode logic.
Full decoding is still performed in the execution stage with the full decode results checked against the pre-decode blanking control.
If the full decode disagrees with the pre-decode OTBN raises a `BAD_INTERNAL_STATE` fatal error.

Blanking is applied in the following locations:

* Read path from the bignum, CSR and WDR register files.
  This is achieved with a one-hot mux with a two-level AND-OR structure.
* Write data into the bignum, CSR and WDR register files.
  Blanking is done separately for each register (as opposed to once on incoming write data that fans out to each register).
* All relevant data paths within the bignum ALU and MAC.
  Data paths not required for the instruction being executed are blanked.

Note there is no blanking on the base side (save for the CSRs as these provide access to WDRs such as ACC).

# References

<a name="ref-chen08">[CHEN08]</a> L. Chen, "Hsiao-Code Check Matrices and Recursively Balanced Matrices," arXiv:0803.1217 [cs], Mar. 2008 [Online]. Available: https://arxiv.org/abs/0803.1217

<a name="ref-symbiotic21">[SYMBIOTIC21]</a> RISC-V Bitmanip Extension v0.93 Available: https://github.com/riscv/riscv-bitmanip/releases/download/v0.93/bitmanip-0.93.pdf
