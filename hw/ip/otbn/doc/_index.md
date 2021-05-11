---
title: OpenTitan Big Number Accelerator (OTBN) Technical Specification
---

# Overview

This document specifies functionality of the OpenTitan Big Number Accelerator, or OTBN.
OTBN is a coprocessor for asymmetric cryptographic operations like RSA or Elliptic Curve Cryptography (ECC).

This module conforms to the [Comportable guideline for peripheral functionality]({{< relref "doc/rm/comportability_specification" >}}).
See that document for integration overview within the broader top level system.

## Features

* Processor optimized for wide integer arithmetic
* 32b wide control path with 32 32b wide registers
* 256b wide data path with 32 256b wide registers
* Full control-flow support with conditional branch and unconditional jump instructions, hardware loops, and hardware-managed call/return stacks.
* Reduced, security-focused instruction set architecture for easier verification and the prevention of data leaks.
* Built-in access to random numbers.
  Note: The (quality) properties of the provided random numbers are not currently specified; this gap in the specification will be addressed in a future revision.

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
The full ISA description can be found in our [ISA manual]({{< relref "isa" >}}).
The instruction set is split into two groups:

* The **base instruction subset** operates on the 32b General Purpose Registers (GPRs).
  Its instructions are used for the control flow of a OTBN application.
  The base instructions are inspired by RISC-V’s RV32I instruction set, but not compatible with it.
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
See the documentation for [`JAL`]({{< relref "isa#jal" >}}) and [`JALR`]({{< relref "isa#jalr" >}}) for a description of how to use it for this purpose.

The call stack has a maximum depth of 8 elements.
Each instruction that reads from `x1` pops a single element from the stack.
Each instruction that writes to `x1` pushes a single element onto the stack.
An instruction that reads from an empty stack or writes to a full stack causes OTBN to stop, raising an alert and setting the `ErrBitCallStack` bit in the {{< regref "ERR_BITS" >}} register.

A single instruction can both read and write to the stack.
In this case, the read is ordered before the write.
Providing the stack has at least one element, this is allowed, even if the stack is full.

### Control and Status Registers (CSRs)

Control and Status Registers (CSRs) are 32b wide registers used for "special" purposes, as detailed in their description;
they are not related to the GPRs.
CSRs can be accessed through dedicated instructions, `CSRRS` and `CSRRW`.
Writes to read-only registers are ignored; they do not signal an error.
All RW CSRs are set to 0 when OTBN starts (when 1 is written to {{< regref "CMD.start" >}}).

<!-- This list of CSRs is replicated in the RTL, in otbn_env_cov.sv and in csr.py.
     If editing one, edit the other three as well. -->
<table>
  <thead>
    <tr>
      <th>Number</th>
      <th>Privilege</th>
      <th>Description</th>
    </tr>
  </thead>
  <tbody>
    <tr>
      <td>0x7C0</td>
      <td>RW</td>
      <td>
        <strong>FG0</strong>.
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
      <td>
        <strong>FG1</strong>.
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
      <td>
        <strong>FLAGS</strong>.
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
      <td>
        <strong>MOD0</strong>.
        Bits [31:0] of the modulus operand, used in the BN.ADDM/BN.SUBM instructions.
        This CSR is mapped to the MOD WSR.
      </td>
    </tr>
    <tr>
      <td>0x7D1</td>
      <td>RW</td>
      <td>
        <strong>MOD1</strong>.
        Bits [63:32] of the modulus operand, used in the BN.ADDM/BN.SUBM instructions.
        This CSR is mapped to the MOD WSR.
      </td>
    </tr>
    <tr>
      <td>0x7D2</td>
      <td>RW</td>
      <td>
        <strong>MOD2</strong>.
        Bits [95:64] of the modulus operand, used in the BN.ADDM/BN.SUBM instructions.
        This CSR is mapped to the MOD WSR.
      </td>
    </tr>
    <tr>
      <td>0x7D3</td>
      <td>RW</td>
      <td>
        <strong>MOD3</strong>.
        Bits [127:96] of the modulus operand, used in the BN.ADDM/BN.SUBM instructions.
        This CSR is mapped to the MOD WSR.
      </td>
    </tr>
    <tr>
      <td>0x7D4</td>
      <td>RW</td>
      <td>
        <strong>MOD4</strong>.
        Bits [159:128] of the modulus operand, used in the BN.ADDM/BN.SUBM instructions.
        This CSR is mapped to the MOD WSR.
      </td>
    </tr>
    <tr>
      <td>0x7D5</td>
      <td>RW</td>
      <td>
        <strong>MOD5</strong>.
        Bits [191:160] of the modulus operand, used in the BN.ADDM/BN.SUBM instructions.
        This CSR is mapped to the MOD WSR.
      </td>
    </tr>
    <tr>
      <td>0x7D6</td>
      <td>RW</td>
      <td>
        <strong>MOD6</strong>.
        Bits [223:192] of the modulus operand, used in the BN.ADDM/BN.SUBM instructions.
        This CSR is mapped to the MOD WSR.
      </td>
    </tr>
    <tr>
      <td>0x7D7</td>
      <td>RW</td>
      <td>
        <strong>MOD7</strong>.
        Bits [255:224] of the modulus operand, used in the BN.ADDM/BN.SUBM instructions.
        This CSR is mapped to the MOD WSR.
      </td>
    </tr>
    <tr>
      <td>0xFC0</td>
      <td>R</td>
      <td>
        <strong>RND</strong>.
        A random number.
        The number is sourced from the EDN via a single-entry cache.
        Reads when the cache is empty will cause OTBN to be stalled until a new random number is available.
      </td>
    </tr>
    <tr>
      <td>0xFC1</td>
      <td>RW</td>
      <td>
        <strong>RND_PREFETCH</strong>.
        Write to this CSR to begin a request to fill the RND cache.
        Always reads as 0.
      </td>
    </tr>
    <tr>
      <td>0xFC2</td>
      <td>R</td>
      <td>
        <strong>URND</strong>.
        A random number.
        The number is sourced from an LFSR.
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
They can be accessed with the [`BN.WSRRS`]({{< relref "isa#bnwsrrs" >}}) and [`BN.WSRRW`]({{< relref "isa#bnwsrrw" >}}) instructions.
Writes to read-only registers are ignored; they do not signal an error.
All RW WSRs are set to 0 when OTBN starts (when 1 is written to {{< regref "CMD.start" >}}).

<table>
  <thead>
    <tr>
      <th>Number</th>
      <th>Name</th>
      <th>R/W</th>
      <th>Description</th>
    </tr>
  </thead>
  <tbody>
    <tr>
      <td>0x0</td>
      <td><strong>MOD</strong></td>
      <td>RW</td>
<td>

The modulus used by the [`BN.ADDM`]({{< relref "isa#bnaddm" >}}) and [`BN.SUBM`]({{< relref "isa#bnsubm" >}}) instructions.
This WSR is also visible as CSRs `MOD0` through to `MOD7`.

</td>
    </tr>
    <tr>
      <td>0x1</td>
      <td><strong>RND</strong></td>
      <td>R</td>
      <td>
        A random number.
        The number is sourced from the EDN via a single-entry cache.
        Reads when the cache is empty will cause OTBN to be stalled until a new random number is fetched from the EDN.
      </td>
    </tr>
    <tr>
      <td>0x2</td>
      <td><strong>ACC</strong></td>
      <td>RW</td>
      <td>
        The accumulator register used by the BN.MULQACC instruction.
      </td>
    </tr>
    <tr>
      <td>0x3</td>
      <td><strong>URND</strong></td>
      <td>R</td>
      <td>
        A random number.
        The number is sourced from an LFSR.
        Reads never stall.
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

OTBN has two instructions for hardware-assisted loops: [`LOOP`]({{< relref "isa#loop" >}}) and [`LOOPI`]({{< relref "isa#loopi" >}}).
Both use the same state for tracking control flow.
This is a stack of tuples containing a loop count, start address and end address.
The stack has a maximum depth of eight and the top of the stack is the current loop.

# Security Features

<div class="bd-callout bd-callout-warning">
  <h5>Work in progress</h5>

  Work on OTBN is ongoing, including work on the specification and implementation of its security features.
  Do not treat the following description (or anything in this documentation) as final, fully implemented, or verified.
</div>

OTBN is a security co-processor.
It contains various security features and is hardened against side-channel analysis and fault injection attacks.
The following sections describe the high-level security features of OTBN.
Refer to the [Design Details]({{< relref "#design-details" >}}) section for a more in-depth description.

## Data Integrity Protection

OTBN's data integrity protection is designed to protect the data stored and processed within OTBN from modifications through physical attacks.

Data in OTBN travels along a data path which includes the data memory (DMEM), the load-store-unit (LSU), the register files (GPR and WDR), and the execution units.
Whenever possible, data transmitted or stored within OTBN is protected with an integrity protection code which guarantees the detection of at least three modified bits per 32 bit word.
Additionally, instructions and data stored in the instruction and data memory, respectively, are scrambled with a lightweight, non-cryptographically-secure cipher.

Refer to the [Data Integrity Protection]({{<relref "#design-details-data-integrity-protection">}}) section for details of how the data integrity protections are implemented.

# Theory of Operations

## Block Diagram

![OTBN architecture block diagram](otbn_blockarch.svg)

## Hardware Interfaces

{{< incGenFromIpDesc "../data/otbn.hjson" "hwcfg" >}}

## Design Details {#design-details}

### Memories

The OTBN processor core has access to two dedicated memories: an instruction memory (IMEM), and a data memory (DMEM).
Each memory is 4 kiB in size.

The memory layout follows the Harvard architecture.
Both memories are byte-addressed, with addresses starting at 0.

The instruction memory (IMEM) is 32b wide and provides the instruction stream to the OTBN processor.
It cannot be read from or written to by user code through load or store instructions.

The data memory (DMEM) is 256b wide and read-write accessible from the base and big number instruction subsets of the OTBN processor core.
There are four instructions that can access data memory.
In the base instruction subset, there are `LW` (load word) and `SW` (store word).
These access 32b-aligned 32b words.
In the big number instruction subset, there are `BN.LID` (load indirect) and `BN.SID` (store indirect).
These access 256b-aligned 256b words.

Both memories can be accessed through OTBN's register interface ({{< regref "DMEM" >}} and {{< regref "IMEM" >}}).
These accesses are ignored if OTBN is busy.
A host processor can check whether OTBN is busy by reading the {{< regref "STATUS.busy">}} flag.
All memory accesses through the register interface must be word-aligned 32b word accesses.

### Random Numbers

OTBN is connected to the [Entropy Distribution Network (EDN)]({{< relref "hw/ip/edn/doc" >}}) which can provide random numbers via the `RND` and `URND` CSRs and WSRs.

`RND` provides bits taken directly from the EDN.
As an EDN request can take time, `RND` is backed by a single-entry cache containing the result of the most recent EDN request.
A read from `RND` empties this cache.
A prefetch into the cache, which can be used to hide the EDN latency, is triggered on any write to the `RND_PREFETCH` CSR.
Writes to `RND_PREFETCH` will be ignored whilst a prefetch is in progress or when the cache is already full.
OTBN will stall until the request provides bits.
Both the `RND` CSR and WSR take their bits from the same cache.
`RND` CSR reads simply discard the other 192 bits on a read.
When stalling on an `RND` read, OTBN will unstall on the cycle after `otbn_core` receives WLEN RND data from the EDN.

`URND` provides bits from an LFSR; reads from it never stall.
The `URND` LFSR is seeded once from the EDN when OTBN starts execution.
Each new execution of OTBN will reseed the `URND` LFSR.
The LFSR state is advanced every cycle when OTBN is running.

### Error Handling and Reporting {#design-details-error-handling-and-reporting}

By design, OTBN is a simple processor and provides no error handling support to code that runs on it.

Whenever OTBN observes an error, it will generate an alert.
This gets sent to the alert manager.
The alert will either be fatal or recoverable, depending on the class of error: see [Alerts]({{< relref "#alerts" >}}) and {{< regref "ERR_BITS" >}} below for details.

If OTBN was running when the alert occurred (this is true whenever {{< regref "STATUS.busy" >}} is high), it will also:
- Immediately stop fetching and executing instructions.
- Set {{< regref "INTR_STATE.done" >}} and clear {{< regref "STATUS.busy" >}}, marking the operation as completed.
- Set the {{< regref "ERR_BITS" >}} register to a non-zero value describing the error.

Note that OTBN can detect some errors even when it isn't running.
One example of this is an error caused by an ECC failure when reading or programming OTBN's memories over the bus.
In this case, the {{< regref "ERR_BITS" >}} register will not change.
This avoids race conditions with the host processor's error handling software.
However, every error that OTBN detects when it isn't running causes a fatal alert.
This means that the cause will be reflected in {{< regref "FATAL_ALERT_CAUSE" >}}, as described below in [Alerts]({{< relref "#alerts" >}}).
This way, no alert is generated without setting an error code somewhere.

<div class="bd-callout bd-callout-warning">
  <h5>TODO</h5>

  When the implementation is finished, document more precisely how OTBN stops on error.
  Can we claim to cancel all register and memory writes in that cycle?
  Is there a way for that to make sense for errors that aren't related to a particular instruction (e.g. shadow register mis-matches; FSM glitches)?

  Also, once it is decided, document behaviour on a bus access when OTBN is running.
</div>

### Alerts

OTBN has two alerts, one recoverable and one fatal.
The {{< regref "ERR_BITS" >}} register documentation has a detailed list of error conditions, those with 'fatal' in the name raise a **fatal alert**, otherwise they raise a **recoverable alert**.

A **recoverable alert** is a one-time triggered alert for recoverable error conditions.
Recoverable alerts are only triggered when OTBN is running, so will always imply a write to {{< regref "ERR_BITS" >}}.
The error that caused the alert can be determined by reading the {{< regref "ERR_BITS" >}} register.

A **fatal alert** is a continuously triggered alert after unrecoverable error conditions.
The error that caused the alert can be determined by reading the {{< regref "FATAL_ALERT_CAUSE" >}} register.
If OTBN was running, this value will also be reflected in the {{< regref "ERR_BITS" >}} register.
A fatal alert can only be cleared by resetting OTBN through the `rst_ni` line.

### Idle

OTBN exposes a single-bit `idle_o` signal, intended to be used by the clock manager to clock-gate the block when it is not in use.
This signal is high when OTBN is not running.
The cycle after a write to {{< regref "CMD.start" >}}, the signal goes low.
This remains low until the end of the operation (either from an [`ECALL`]({{< relref "isa#ecall" >}}) or an error, at which point it goes high again.

### Data Integrity Protection {#design-details-data-integrity-protection}

OTBN stores and operates on data (state) in its dedicated memories, register files, and internal registers.
OTBN's data integrity protection is designed to protect all data stored and transmitted within OTBN from modifications through physical attacks.

During transmission, the integrity of data is protected with an integrity protection code.
Data at rest in the instruction and data memories is additionally scrambled.

In the following, the Integrity Protection Code and the scrambling algorithm are discussed, followed by their application to individual storage elements.

#### Integrity Protection Code {#design-details-integrity-protection-code}

OTBN uses the same integrity protection code everywhere to provide overarching data protection without regular re-encoding.
The code is applied to 32b data words, and produces 39b of encoded data.

The code used is an (39,32) Hsiao "single error correction, double error detection" (SECDED) error correction code (ECC) [[CHEN08]({{< relref "#ref-chen08">}})].
It has a minimum Hamming distance of four, resulting in the ability to detect at least three errors in a 32 bit word.
The code is used for error detection only; no error correction is performed.

#### Memory Scrambling {#design-details-memory-scrambling}

Contents of OTBN's instruction and data memories are scrambled while at rest.
The data is bound to the address and scrambled before being stored in memory.
The addresses are randomly remapped.

Note that data stored in other temporary memories within OTBN, including the register files, is not scrambled.

Scrambling is used to obfuscate the memory contents and to diffuse the data.
Obfuscation makes passive probing more difficult, while diffusion makes active fault injection attacks more difficult.

The scrambling mechanism is described in detail in the [section "Scrambling Primitive" of the SRAM Controller Technical Specification](/hw/ip/sram_ctrl/doc/#scrambling-primitive).

The scrambling keys are rotated regularly, refer to the sections below for more details.

#### Actions on Integrity Errors

A fatal error is raised whenever a data integrity violation is detected, which results in an immediate stop of all processing and the issuing of a fatal alert.
The section [Error Handling and Reporting]({{< relref "#design-details-error-handling-and-reporting" >}}) describes the error handling in more detail.

#### Register File Integrity Protection

OTBN contains two register files: the 32b GPRs and the 256b WDRs.
The data stored in both register files is protected with the [Integrity Protection Code]({{< relref "#design-details-integrity-protection-code">}}).
Neither the register file contents nor register addresses are scrambled.

The GPRs `x2` to `x31` store a 32b data word together with the Integrity Protection Code, resulting in 39b of stored data.
(`x0`, the zero register, and `x1`, the call stack, require special treatment.)

Each 256b Wide Data Register (WDR) stores a 256b data word together with the Integrity Protection Code, resulting in 312b of stored data.
The integrity protection is done separately for each of the eight 32b sub-words within a 256b word.

The register files can consume data protected with the Integrity Protection Code, or add it on demand.
Whenever possible the Integrity Protection Code is preserved from its source and written directly to the register files without recalculation, in particular in the following cases:

* Data coming from the data memory (DMEM) through the load-store unit to a GPR or WDR.
* Data copied between WDRs using the `BN.MOV` or `BN.MOVR` instructions.
* Data conditionally copied between WDRs using the `BN.SEL` instruction.
* Data copied between the `ACC` and `MOD` WSRs and a WDR.
  (TODO: Not yet implemented.)
* Data copied between any of the `MOD0` to `MOD7` CSRs and a GPR.
  (TODO: Not yet implemented.)

In all other cases the register files add the Integrity Protection Code to the incoming data before storing the data word.

The integrity protection bits are checked on every read from the register files, even if the integrity protection is not removed from the data.

Detected integrity violations in a register file raise a fatal `reg_error`.

#### Data Memory (DMEM) Integrity Protection

OTBN's data memory is 256b wide, but allows for 32b word accesses.
To facilitate such accesses, all integrity protection in the data memory is done on a 32b word granularity.

All data entering or leaving the data memory block is protected with the [Integrity Protection Code]({{< relref "#design-details-integrity-protection-code">}});
this code is not re-computed within the memory block.

Before being stored in SRAM, the data word with the attached Integrity Protection Code, as well as the address are scrambled according to the [memory scrambling algorithm]({{< relref "#design-details-memory-scrambling">}}).
The scrambling is reversed on a read.

The ephemeral memory scrambling key and the nonce are provided by the [OTP block]({{<relref "/hw/ip/otp_ctrl/doc" >}}).
They are set once when OTBN block is reset, and changed whenever a secure wipe of the data memory is performed.
(TODO: Link to it once we have specified secure wipe.)

The Integrity Protection Code is checked on every memory read, even though the code remains attached to the data.
A further check must be performed when the data is consumed.
Detected integrity violations in the data memory raise a fatal `dmem_error`.

#### Instruction Memory (IMEM) Integrity Protection

All data entering or leaving the instruction memory block is protected with the [Integrity Protection Code]({{< relref "#design-details-integrity-protection-code">}});
this code is not re-computed within the memory block.

Before being stored in SRAM, the instruction word with the attached Integrity Protection Code, as well as the address are scrambled according to the [memory scrambling algorithm]({{< relref "#design-details-memory-scrambling">}}).
The scrambling is reversed on a read.

The ephemeral memory scrambling key and the nonce are provided by the [OTP block]({{<relref "/hw/ip/otp_ctrl/doc" >}}).
They are set once when OTBN block is reset, and changed whenever a secure wipe of the instruction memory is performed.
(TODO: Link to it once we have specified secure wipe.)

The Integrity Protection Code is checked on every memory read, even though the code remains attached to the data.
A further check must be performed when the data is consumed.
Detected integrity violations in the data memory raise a fatal `imem_error`.

# Running applications on OTBN

OTBN is a specialized coprocessor which is used from the host CPU.
This section describes how to interact with OTBN from the host CPU to execute an existing OTBN application.
The section [Writing OTBN applications]({{< ref "#writing-otbn-applications" >}}) describes how to write such applications.

## High-level operation sequence

The high-level sequence by which the host processor should use OTBN is as follows.

1. Write the OTBN application binary to {{< regref "IMEM" >}}, starting at address 0.
2. Optional: Write constants and input arguments, as mandated by the calling convention of the loaded application, to {{< regref "DMEM" >}}.
3. Start the operation on OTBN by writing `1` to {{< regref "CMD.start" >}}.
   Now neither data nor instruction memory may be accessed from the host CPU.
   After it has been started the OTBN application runs to completion without further interaction with the host.
4. Wait for the operation to complete (see below).
   As soon as the OTBN operation has completed the data and instruction memories can be accessed again from the host CPU.
5. Check if the operation was successful by reading the {{< regref "ERR_BITS" >}} register.
6. Optional: Retrieve results by reading {{< regref "DMEM" >}}, as mandated by the calling convention of the loaded application.

OTBN applications are run to completion.
The host CPU can determine if an application has completed by either polling {{< regref "STATUS.busy">}} or listening for an interrupt.

* To poll for a completed operation, software should repeatedly read the {{< regref "STATUS.busy" >}} register.
  While the operation is in progress, {{< regref "STATUS.busy" >}} reads as `1`.
  The operation is completed if {{< regref "STATUS.busy" >}} is `0`.
* Alternatively, software can listen for the `done` interrupt to determine if the operation has completed.
  The standard sequence of working with interrupts has to be followed, i.e. the interrupt has to be enabled, an interrupt service routine has to be registered, etc.
  The [DIF]({{<relref "#dif" >}}) contains helpers to do so conveniently.

Note: This operation sequence only covers functional aspects.
Depending on the application additional steps might be necessary, such as deleting secrets from the memories.

## Device Interface Functions (DIFs) {#dif}

{{< dif_listing "sw/device/lib/dif/dif_otbn.h" >}}

## Driver {#driver}

A higher-level driver for the OTBN block is available at `sw/device/lib/runtime/otbn.h` ([API documentation](/sw/apis/otbn_8h.html)).

## Register Table

{{< incGenFromIpDesc "../data/otbn.hjson" "registers" >}}

# Writing OTBN applications {#writing-otbn-applications}

OTBN applications are (small) pieces of software written in OTBN assembly.
The full instruction set is described in the [ISA manual]({{< relref "isa" >}}), and example software is available in the `sw/otbn` directory of the OpenTitan source tree.

A hands-on user guide to develop OTBN software can be found in the section [Writing and building software for OTBN]({{<relref "doc/ug/otbn_sw.md" >}}).

## Toolchain support

OTBN comes with a toolchain consisting of an assembler, a linker, and helper tools such as objdump.
The toolchain wraps a RV32 GCC toolchain and supports many of its features.

The following tools are available:
* `otbn-as`: The OTBN assembler.
* `otbn-ld`: The OTBN linker.
* `otbn-objdump`: objdump for OTBN.

Other tools from the RV32 toolchain can be used directly, such as objcopy.

## Passing of data between the host CPU and OTBN {#writing-otbn-applications-datapassing}

Passing data between the host CPU and OTBN is done through the data memory (DMEM).
No standard or required calling convention exists, every application is free to pass data in and out of OTBN in whatever format it finds convenient.
All data passing must be done when OTBN is not running, as indicated by the {{< regref "STATUS.busy" >}} bit; during the OTBN operation both the instruction and the data memory are inaccessible from the host CPU.

## Returning from an application

The software running on OTBN signals completion by executing the [`ECALL`]({{< relref "isa#ecall" >}}) instruction.

When it executes this instruction, OTBN:
- Stops fetching and executing instructions.
- Sets {{< regref "INTR_STATE.done" >}} and clears {{< regref "STATUS.busy" >}}, marking the operation as completed.
- Writes zero to {{< regref "ERR_BITS" >}}.

The DMEM can be used to pass data back to the host processor, e.g. a "return value" or an "exit code".
Refer to the section [Passing of data between the host CPU and OTBN]({{<relref "#writing-otbn-applications-datapassing" >}}) for more information.

## Using hardware loops

OTBN provides two hardware loop instructions: `LOOP` and `LOOPI`.

### Loop nesting

OTBN permits loop nesting and branches and jumps inside loops.
However, it doesn't have support for early termination of loops: there's no way to pop an entry from the loop stack without executing the last instruction of the loop the correct number of times.
It can also only pop one level of the loop stack per instruction.

To avoid polluting the loop stack and avoid surprising behaviour, the programmer must ensure that:
* Even if there are branches and jumps within a loop body, the final instruction of the loop body gets executed exactly once per iteration.
* Nested loops have distinct end addresses.
* The end instruction of an outer loop is not executed before an inner loop finishes.

OTBN does not detect these conditions being violated, so no error will be signalled should they occur.

(Note indentation in the code examples is for clarity and has no functional impact.)

The following loops are *well nested*:

```
LOOP x2, 3
  LOOP x3, 1
    ADDI x4, x4, 1
  # The NOP ensures that the outer and inner loops end on different instructions
  NOP

# Both inner and outer loops call some_fn, which returns to
# the body of the loop
LOOP x2, 5
  JAL x1, some_fn
  LOOP x3, 2
    JAL x1, some_fn
    ADDI x4, x4, 1
  NOP

# Control flow leaves the immediate body of the outer loop but eventually
# returns to it
LOOP x2, 4
  BEQ x4, x5, some_label
branch_back:
  LOOP x3, 1
    ADDI x6, x6, 1
  NOP

some_label:
  ...
  JAL x0, branch_back
```

The following loops are not well nested:

```
# Both loops end on the same instruction
LOOP x2, 2
  LOOP x3, 1
    ADDI x4, x4, 1

# Inner loop jumps into outer loop body (executing the outer loop end
# instruction before the inner loop has finished)
LOOP x2, 5
  LOOP x3, 3
    ADDI x4, x4 ,1
    BEQ  x4, x5, outer_body
    ADD  x6, x7, x8
outer_body:
  SUBI  x9, x9, 1
```

## Algorithic Examples: Multiplication with BN.MULQACC

The big number instruction subset of OTBN generally operates on WLEN bit numbers.
`BN.MULQACC` operates with WLEN/4 bit operands (with a full WLEN accumulator).
This section outlines two techniques to perform larger multiplies by composing multiple `BN.MULQACC` instructions.

### Multiplying two WLEN/2 numbers with BN.MULQACC

This instruction sequence multiplies the lower half of `w0` by the upper half of
`w0` placing the result in `w1`.

```
BN.MULQACC.Z      w0.0, w0.2, 0
BN.MULQACC        w0.0, w0.3, 64
BN.MULQACC        w0.1, w0.2, 64
BN.MULQACC.WO w1, w0.1, w0.3, 128
```

### Multiplying two WLEN numbers with BN.MULQACC

The shift out functionality can be used to perform larger multiplications without extra adds.
The table below shows how two registers `w0` and `w1` can be multiplied together to give a result in `w2` and `w3`.
The cells on the right show how the result is built up `a0:a3 = w0.0:w0.3` and `b0:b3 = w1.0:w1.3`.
The sum of a column represents WLEN/4 bits of a destination register, where `c0:c3 = w2.0:w2.3` and `d0:d3 = w3.0:w3.3`.
Each cell with a multiply in takes up two WLEN/4-bit columns to represent the WLEN/2-bit multiply result.
The current accumulator in each instruction is represented by highlighted cells where the accumulator value will be the sum of the highlighted cell and all cells above it.

The outlined technique can be extended to arbitrary bit widths but requires unrolled code with all operands in registers.

<table>
  <thead>
    <tr>
      <th></th>
      <th>d3</th>
      <th>d2</th>
      <th>d1</th>
      <th>d0</th>
      <th>c3</th>
      <th>c2</th>
      <th>c1</th>
      <th>c0</th>
    </tr>
  </thead>
  <tbody>
    <tr>
      <td><code>BN.MULQACC.Z w0.0, w1.0, 0</code></td>
      <td></td>
      <td></td>
      <td></td>
      <td></td>
      <td style="background-color: orange"></td>
      <td style="background-color: orange"></td>
      <td style="background-color: orange" colspan="2" rowspan="1"><code>a0 * b0</code></td>
    </tr>
    <tr>
      <td><code>BN.MULQACC w0.1, w1.0, 64</code></td>
      <td></td>
      <td></td>
      <td></td>
      <td></td>
      <td style="background-color: orange"></td>
      <td style="background-color: orange" colspan="2" rowspan="1"><code>a1 * b0</code></td>
      <td style="background-color: orange"></td>
    </tr>
    <tr>
      <td><code>BN.MULQACC.SO w2.l, w0.0, w1.1, 64</code></td>
      <td></td>
      <td></td>
      <td></td>
      <td></td>
      <td style="background-color: orange"></td>
      <td style="background-color: orange" colspan="2" rowspan="1"><code>a0 * b1</code></td>
      <td style="background-color: orange"></td>
    </tr>
    <tr>
      <td><code>BN.MULQACC w0.2, w1.0, 0</code></td>
      <td></td>
      <td></td>
      <td style="background-color: yellow"></td>
      <td style="background-color: yellow"></td>
      <td style="background-color: yellow" colspan="2" rowspan="1"><code>a2 * b0</code></td>
      <td></td>
      <td></td>
    </tr>
    <tr>
      <td><code>BN.MULQACC w0.1, w1.1, 0</code></td>
      <td></td>
      <td></td>
      <td style="background-color: yellow"></td>
      <td style="background-color: yellow"></td>
      <td style="background-color: yellow" colspan="2" rowspan="1"><code>a1 * b1</code></td>
      <td></td>
      <td></td>
    </tr>
    <tr>
      <td><code>BN.MULQACC w0.0, w1.2, 0</code></td>
      <td></td>
      <td></td>
      <td style="background-color: yellow"></td>
      <td style="background-color: yellow"></td>
      <td style="background-color: yellow" colspan="2" rowspan="1"><code>a0 * b2</code></td>
      <td></td>
      <td></td>
    </tr>
    <tr>
      <td><code>BN.MULQACC w0.3, w1.0, 64</code></td>
      <td></td>
      <td></td>
      <td style="background-color: yellow"></td>
      <td style="background-color: yellow" colspan="2" rowspan="1"><code>a3 * b0</code></td>
      <td style="background-color: yellow"></td>
      <td></td>
      <td></td>
    </tr>
    <tr>
      <td><code>BN.MULQACC w0.2, w1.1, 64</code></td>
      <td></td>
      <td></td>
      <td style="background-color: yellow"></td>
      <td style="background-color: yellow" colspan="2" rowspan="1"><code>a2 * b1</code></td>
      <td style="background-color: yellow"></td>
      <td></td>
      <td></td>
    </tr>
    <tr>
      <td><code>BN.MULQACC w0.1, w1.2, 64</code></td>
      <td></td>
      <td></td>
      <td style="background-color: yellow"></td>
      <td style="background-color: yellow" colspan="2" rowspan="1"><code>a1 * b2</code></td>
      <td style="background-color: yellow"></td>
      <td></td>
      <td></td>
    </tr>
    <tr>
      <td><code>BN.MULQACC.SO w2.u, w0.0, w1.3, 64</code></td>
      <td></td>
      <td></td>
      <td style="background-color: yellow"></td>
      <td style="background-color: yellow" colspan="2" rowspan="1"><code>a0 * b3</code></td>
      <td style="background-color: yellow"></td>
      <td></td>
      <td></td>
    </tr>
    <tr>
      <td><code>BN.MULQACC w0.3, w1.1, 0</code></td>
      <td style="background-color: olive"></td>
      <td style="background-color: olive"></td>
      <td style="background-color: olive" colspan="2" rowspan="1"><code>a3 * b1</code></td>
      <td></td>
      <td></td>
      <td></td>
      <td></td>
    </tr>
    <tr>
      <td><code>BN.MULQACC w0.2, w1.2, 0</code></td>
      <td style="background-color: olive"></td>
      <td style="background-color: olive"></td>
      <td style="background-color: olive" colspan="2" rowspan="1"><code>a2 * b2</code></td>
      <td></td>
      <td></td>
      <td></td>
      <td></td>
    </tr>
    <tr>
      <td><code>BN.MULQACC w0.1, w1.3, 0</code></td>
      <td style="background-color: olive"></td>
      <td style="background-color: olive"></td>
      <td style="background-color: olive" colspan="2" rowspan="1"><code>a1 * b3</code></td>
      <td></td>
      <td></td>
      <td></td>
      <td></td>
    </tr>
    <tr>
      <td><code>BN.MULQACC w0.3, w1.2, 64</code></td>
      <td style="background-color: olive"></td>
      <td style="background-color: olive" colspan="2" rowspan="1"><code>a3 * b2</code></td>
      <td style="background-color: olive"></td>
      <td></td>
      <td></td>
      <td></td>
      <td></td>
    </tr>
    <tr>
      <td><code>BN.MULQACC.SO w3.l, w0.2, w1.3, 64</code></td>
      <td style="background-color: olive"></td>
      <td style="background-color: olive" colspan="2" rowspan="1"><code>a2 * b3</code></td>
      <td style="background-color: olive"></td>
      <td></td>
      <td></td>
      <td></td>
      <td></td>
    </tr>
    <tr>
      <td><code>BN.MULQACC.SO w3.u, w0.3, w1.3, 0</code></td>
      <td style="background-color: lightblue" colspan="2" rowspan="1"><code>a3 * b3</code></td>
      <td></td>
      <td></td>
      <td></td>
      <td></td>
      <td></td>
      <td></td>
    </tr>
  </tbody>
</table>

Code snippets giving examples of 256x256 and 384x384 multiplies can be found in `sw/otbn/code-snippets/mul256.s` and `sw/otbn/code-snippets/mul384.s`.

# References

<a name="ref-chen08">[CHEN08]</a> L. Chen, "Hsiao-Code Check Matrices and Recursively Balanced Matrices," arXiv:0803.1217 [cs], Mar. 2008 [Online]. Available: http://arxiv.org/abs/0803.1217
