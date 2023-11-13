# Secure Hardware Design Guidelines

## Overview

Silicon designs for security devices require special guidelines to protect the
designs against myriad attacks. For OpenTitan, the universe of potential attacks
is described in our threat model. In order to have the most robust defensive
posture, a general approach to secure hardware design should rely on the
concepts of (1) defense in depth, (2) consideration of recovery methods
post-breach, and (3) thinking with an attacker mindset.

In all cases, as designers, we need to think of equalizing the difficulty of any
particular attack for the adversary. If a design has a distribution of attack
vectors (sometimes called the "attack surface" or "attack surface area"), it is
not the strength of the strongest defenses that is particularly of interest but
rather the weakest, since these will be the most likely to be exploited by the
adversary. For example, it's unlikely that an attacker will try to brute-force a
system based on AES-128 encryption, as the difficulty level of such an attack is
high, and our confidence in the estimate of the difficulty is also high. But, if
the security of the AES-128 depends on a global secret, more mundane attacks
like theft or bribery become more likely avenues for the adversary to exploit.

Defense in depth means having multiple layers of defenses/controls acting
independently. Classically in information security, these are grouped into three
main categories: physical, technical and administrative[^1]. We map these into
slightly different elements when considering secure hardware design:

*   Physical security typically maps to sensors and shields, but also separation
    of critical information into different locations on the die.
*   Technical security includes techniques like encrypting data-at-rest,
    scrambling buses for data-in-motion, and integrity checking for all kinds of
    data.
*   Administrative security encompasses architectural elements like permissions,
    lifecycle states, and key splits (potentially also linked to physical
    security).

Consideration of recovery methods means assuming that some or all of the
defenses will fail, with an eye to limiting the extent of the resulting system
failure/compromise. If an adversary gains control over a sub-block, but cannot
use this to escalate to full-chip control, we have succeeded. If control over a
sub-block is detected, but an alert is generated that ultimately causes a device
reset or other de-escalation sequence, we have created a recovery strategy. If
the software is compromised but access to keys/secrets is prevented by hardware
controls, we have succeeded. If compromise of secrets from a single device
cannot be leveraged into attacks on other (or all) devices, again we have
succeeded. If compromised devices can be identified and quarantined when
enrolled into a larger system, then we have a successful recovery strategy.

Thinking with an attacker mindset means "breaking the rules" or violating
assumptions: what if two linked state machines no longer are "in sync" - how
will they operate, and how can they recover? What happens if the adversary
manipulates an internal value (fault injection)? What happens if the adversary
can learn some or all of a secret value (side channel leakage)? This document
will primarily try to give generic guidance for defense against the latter two
attacks (fault injection, and side channel information leakage). It also
discusses ways to either prevent attacks, mitigate them, or alert of their
existence. Other attack vectors (especially software compromises or operational
security failures) are not in the scope of this document, or will be addressed
at a later stage.

In general, when thinking of protecting against fault injection attacks, the
designer should consider the consequences of any particular net/node being
inverted or forced by an adversary. State of the art fault attacks can stimulate
two nodes in close succession; robustness to this type of attack depends on the
declared threat model. Designers need to be well aware of the power of an attack
like SIFA [[15](#ref-15)], which can bypass "conventional" fault countermeasures (e.g.
redundancy/detectors) and requires only modest numbers of traces.

For increased resistance against side channel leakage (typically: power,
electromagnetic radiation, or timing), designs in general should ensure that the
creation or transmission of *secret material* is handled in such a way as to not
work with "small" subsets of bits of sensitive information. All side channel attacks
use a strategy of "divide and conquer" to recover *secret material* e.g. word by
word or byte by byte. Making sure to evaluate/process information in 32-bit quanta
or larger will make this more difficult. Attacks like DPA are especially powerful
because on top of such a "divide and conquer" strategy, where e.g. in the case of AES
DPA addresses algorithm-inherent 8-bit intermediate values, they benefit from
statistical analysis of a large number of side channel observations to recover the
correct values.

Below we will go deeper into these recommendations for general design practices.
Individual module guidance for particular IP (processor, AES, SHA, etc) will be
handled in addenda to this document.

## General Module Level Design Guidance

These guidelines are for sub-block / module level design. System architecture,
identity management, and protocol design are outside the scope of this document,
but may create some dependencies here. For general reading, the slides of [[10](#ref-10)]
are considered a useful companion to these guidelines.

### **Recommendation 1**: Identify sensitive/privileged operations

Identify any sensitive/privileged operations performed by the module
(non-exhaustive list of examples: working with secret keys, writing to OTP,
potentially writing to flash, enabling debug functionality, lifting/releasing
access restrictions, changing lifecycle state)

1.  Having these operations documented helps to analyze the potential issues of
    any attack discussed below.
2.  Subsequent design/verification reviews can use these sensitive operations as
    focus areas or even coverage points.

### **Recommendation 2**: Side-channel leakage considerations

Consider side-channel leakage of any secret information (side channels include
timing, power, EM radiation, caches, and micro-architectural state, among
others)

1.  Process secret information in at least a 32-bit wide datapath
2.  Use fixed/constant time operations when handling secrets (see [[6](#ref-6)] and [[11](#ref-11)])
3.  Don't branch/perform conditional operations based on secret values
4.  Incorporate temporal randomness (example: add delay cycles based on LFSR
    around critical operations, see [[9](#ref-9)])
5.  Cryptographic operations should incorporate entropy (via masking/blinding,
    see [[9](#ref-9)]), especially if the key is long-lived, or a global/class-wide value.
    Short-lived keys may not require this, but careful study of the information
    leakage rate is necessary
6.  Noise generation - run other "chaff" switching actions in parallel with
    sensitive calculations, if power budget permits (see [[9](#ref-9)])
7.  Secrets should not be stored in a processor cache (see [[3](#ref-3)])
8.  Speculative execution in a processor can lead to leakage of secrets via
    micro-architectural state (see [[4](#ref-4)]/[[5](#ref-5)])
9.  When clearing secrets, use an LFSR to wipe values to prevent a Hamming
    weight leakage that would occur if clearing to zero. For secrets stored in
    multiple shares, use different permutations (or separate LFSRs) to perform
    the clearing of the shares.

### **Recommendation 3**: Fault injection countermeasures

Consider defenses to fault injection / glitching attacks (survey and overview of
attacks, see [[12](#ref-12)] and [[13](#ref-13)])

1.  Initially assume that the adversary can glitch any node arbitrarily, and
    determine the resulting worst-case scenario. This is a very conservative
    approach and might lead to over-pessimism, but serves to highlight potential
    issues. Then, to ease implementation burden, assume the adversary can glitch
    to all-1's or all-0's (since these are considered "easier" to reach), and
    that reset can be asserted semi-arbitrarily.
2.  Use parity/ECC on memories and data paths (note here that ECC is not true
    integrity, have to use hash to prevent forgery, see [[1](#ref-1)]). For memories, ECC
    is helpful to protect instruction streams or values that can cause
    "branching control flows" that redirect execution flow. Parity is
    potentially helpful if detection of corruption is adequate (though
    double-glitch fault injection can fool parity, so Hsiao or other
    detect-2-error codes can be used, even without correction circuitry
    implemented). When committing to an irrevocable action (e.g. burning into
    OTP, unlocking part of the device/increasing permissions), ECC is probably
    more appropriate.
    1.  When selecting a specific ECC implementation, the error detection
        properties are likely more important than error correction (assuming
        memory lifetime retention/wear are not considered). For a good example
        of how to consider the effectiveness of error correction, see
        [this PR comment](https://github.com/lowRISC/opentitan/pull/3899#issuecomment-716799810).
3.  State machines:
    1.  Have a minimum Hamming distance for state machine transitions, to make
        single bit faults non-effective
    2.  Use a
        [sparsely populated state encoding](https://github.com/lowRISC/opentitan/blob/master/util/design/sparse-fsm-encode.py),
        with all others marked invalid - see 11.1 about optimization concerns
        when doing this though
    3.  All states could have the same Hamming weight, then can constantly check
        for this property (or use ECC-type coding on state variable and check
        this)
    4.  If waiting for a counter to expire to transition to the next state,
        better if the terminal count that causes the transition is not
        all-0/all-1. One could use an LFSR instead of a binary counter, but
        debugging this can be a bit painful then
4.  Maintain value-and-its-complement throughout datapath (sometimes called
    "dual rail" logic), especially if unlocking/enabling something sensitive,
    and continually check for validity/consistency of representation
5.  Incorporate temporal randomness where possible (example: add delay cycles
    based on LFSR around sensitive operations)
6.  Run-it-twice and compare results for sensitive calculations
7.  Redundancy - keep/store multiple copies of sensitive checks/data
8.  For maximum sensitivity, compare combinational and sequential paths with
    hair-trigger/one-shot latch of miscompare
9.  Empty detection for OTP/flash (if needed, but especially for lifecycle
    determination)
10. Avoid local resets / prefer larger reset domains, since a glitch on this
    larger reset keeps more of the design "in sync." But, consider the
    implications of any block with more than one reset domain (see also 9.1).
11. Similar to the "mix in" idea of 4.4, in any case where multiple contributing
    "votes" are going to an enable/unlock decision, consider mixing them into
    some cryptographic structure over time that will be diverted from its path
    by attempts to glitch each vote. (Note: if the final outcome of this is
    simply a wide-compare that produces a single-bit final unlock/enable vote
    then this is only marginally helpful - since that vote is now the glitch
    target. Finding a way to bind the final cryptographic result to the vote is
    preferred, but potentially very difficult / impossible, depending on the
    situation.)
12. When checking/creating a signal to
    <span style="text-decoration:underline;">permit</span> some sensitive
    operation, prefer that the checking logic is maximally volatile (e.g.
    performs a lot of the calculation in a single cycle after a register), such
    that a glitch prevents the operation. Whereas, when checking to
    <span style="text-decoration:underline;">deny</span> a sensitive operation,
    prefer that the checking logic is minimally volatile (is directly following
    a register with minimal combinational logic), such that a glitch will be
    recovered on the next clock and the denial will be continued/preserved.
13. CFI (control flow integrity) hardware can help protect a processor /
    programmable peripheral from some types of glitch attacks. This topic is
    very involved and beyond the scope of these guidelines, consult [[2](#ref-2)]
    for an introduction to previous techniques.
14. Analog sensors (under/over-voltage, laser light, mesh breach, among others)
    can be used to generate SoC-level alerts and/or inhibit sensitive
    operations. Many of these sensors require calibration/trimming, or require
    hysteresis circuits to prevent false-positives, so they may not be usable in
    fast-reacting situations.
15. Running an operation (e.g. AES or KMAC) to completion, even with a detected
    fault, is sometimes useful since it suppresses information for the adversary
    about the success/failure of the attempted fault, and minimizes any timing
    side channel. However, for some operations (e.g. ECDSA sign), operations on
    faulty inputs can have catastrophic consequences. These guidelines cannot
    recommend a default-safe posture, but each decision about handling detected
    faults should be carefully considered.
16. For request-acknowledge interfaces, monitor the acknowledge line for
    spurious pulses at all times (not only when pending request) and use this
    as a glitch/fault detector to escalate locally and/or generate alerts.
17. When arbitrating between two or more transaction sources with different
    privilege/access levels, consider how to protect a request from one source
    being glitched/forged to masquerade as being sourced from another
    higher-privilege source (for example, to return side-loaded
    hardware-visible-only data via a software read path). At a minimum,
    redundant arbitration and multiple-bit encoding of the arbitration "winner"
    can help to mitigate this type of attack.

### **Recommendation 4**: Handling of secrets

1.  Diversify types/sources of secrets (e.g. use combination of RTL constants +
    OTP + flash) to prevent a single compromise from being effective
2.  Rather than "check an unlock value directly" - use a hash function with a
    user-supplied input, and check the output of the hash matches. This way the
    unlock value is not contained in the netlist.
3.  Qualify operations with allowed lifecycle state (even if redundant with
    other checks)
4.  Where possible, mix in operating modes to calculation of derived secrets to
    create parallel/non-substitutable operating/keying domains. (i.e. mixing in
    devmode, lifecycle state)
    1.  If defenses can be bypassed for debugging/recovery, considering mixing
        in activation vector/bypass bits of defenses as well, consider this like
        small-scale attestation of device state
5.  Encrypt (or at least scramble) any secrets stored at-rest in flash/OTP, to
    reduce risks of static/offline inspection.

### **Recommendation 5**: Alerts

1.  Generate alerts on any detected anomaly (need to define what
    priority/severity should be assigned)
2.  Where possible, prefer to take a local action (clearing/randomizing state,
    cease processing) in addition to generating the alert

### **Recommendation 6**: Safe default values

1.  All case statements, if statements, and ternaries should consider what the
    safest default value is. Having an "invalid" state/value is nice to have for
    this purpose, but isn't always possible.
2.  Operate in a general policy/philosophy of starting with lowest allowed
    privilege and augmenting by approvals/unlocks.
3.  Implement enforcement of inputs on CSRs - qualify/force data attempted to be
    written based on lifecycle state, peripheral state, or other values. The
    designer must determine the safest remapping, e.g. write --> read, read -->
    nop, write --> nop and so forth. Blanket implementation of input enforcement
    complicates verification, so this style of design should be chosen only
    where the inputs are particularly sensitive (requests to unlock, privilege
    increase requests, debug mode enables, etc).

### **Recommendation 7**: DFT issues

1.  Entry and exit from scan mode should cause a reset to prevent insertion or
    exfiltration of sensitive values
2.  Ensure that when in production (e.g. not in lab debug) environments, scan
    chains are disabled
3.  Processor debug paths (via JTAG) may need to be disabled in production modes
4.  Beware of self-repair or redundant-row/columns schemes for memories (SRAM
    and OTP), as they can be exploited to misdirect reads to
    adversary-controlled locations

### **Recommendation 8**: Power management issues

1.  If module is not in an always-on power domain, consider that a sleep/wake
    sequence can be used to force a re-derivation of secrets needed in the
    module, as many times as desired by the adversary
2.  Fine-grained clock gating should never be used for any module that processes
    secret data, only coarse-grained (module-level) gating is acceptable. (Fine
    grained gates essentially compute `clock_gate = D ^ Q` which often acts as
    an SCA "amplifier").

### **Recommendation 9**: "Synchronization" (consistency) issues

1.  If a module interacts with other modules in a stateful way (think of two
    data-transfer counters moving in ~lockstep, but the counts are not sent back
    and forth for performance optimization), what happens if:
    1.  One side is reset and the other is not
    2.  One side is clock-gated and the other is not
    3.  One side is power-gated and the other is not
    4.  The counter on one side is glitched
2.  Generally these kind of blind lockstep situations should be avoided where
    possible, and current module/interface status should exchanged in both
    directions and constantly checked for validity/consistency

### **Recommendation 10**: Recovery mechanism considerations

1.  What happens if a security mechanism fails? (Classic problem of this variety
    is on-die sensors being too sensitive and resetting the chip) Traditionally,
    fuses can disable some mechanisms if they are faulty.
2.  Could an adversary exploit a recovery mechanism? (If a sensor can be
    fuse-disabled, wouldn't the adversary just do that? See 4.4 above.)

### **Recommendation 11**: Optimization concerns

1.  Sometimes synthesis will optimize away redundant (but necessary for
    security) logic - `dont_touch` or `size_only` attributes may sometimes be
    needed, or even more aggressive preservation strategies. Example: when using
    the sparse FSM encoding, use the `prim_flop` component for the state vector
    register.
2.  Value-and-complement strategies can also be optimized away, or partially
    disconnected such that only half of the datapath is contributing to the
    logic, or a single register with both Q & Qbar outputs becomes the source of
    both values to save area.
3.  Retiming around pipeline registers can create DPA issues, due to inadvertent
    combination of shares, or intra-cycle glitchy evaluation. For DPA-resistant
    logic, explicitly declare functions and registers using `prim_*` components,
    and make sure that pipeline retiming is not enabled in synthesis.

### **Recommendation 12**: Entropy concerns

1.  Verify that all nonces are truly only used once
2.  If entropy is broadcast, verify list of consumers and arbitration scheme to
    prevent reuse / duplicate use of entropy in sensitive calculations
3.  Seeds for local LFSRs need to be unique/diversified

### **Recommendation 13**: Global secrets

1.  Avoid if at all possible
2.  If not possible, have a process to generate/re-generate them; make sure this
    process is used/tested many times before final netlist; process must be
    repeatable/deterministic given some set of inputs
3.  If architecturally feasible, install a device-specific secret to override
    the global secret once boot-strapped (and disable the global secret)

### **Recommendation 14**: Sensors

1.  Sensors need to be adjusted/tweaked so that they actually fire. It is
    challenging to set the sensors at levels that detect "interesting"
    glitches/environmental effects, but don't fire constantly or cause yield
    issues. Security team should work with the silicon supplier to determine the
    best course of action here.
2.  Sensor configuration / calibration data should be integrity-protected.

### **Recommendation 15**: Reset vs. non-reset flops

The flip-flop type used for registering sensitive assets inside a particular module should be selected later in the design process on a sub-block level and in consideration of all countermeasures and security hardening employed.
For details, refer to [Reset vs. non-reset flops](../reset_vs_non-reset_flops/README.md)

## References and further reading

[<span id="ref-1">1</span>]: Overview of checksums and hashes -
https://cybergibbons.com/reverse-engineering-2/checksums-hashes-and-security/

[<span id="ref-2">2</span>]: A Survey of hardware-based Control Flow Integrity -
https://arxiv.org/pdf/1706.07257.pdf

[<span id="ref-3">3</span>]: Cache-timing attacks on AES -
https://cr.yp.to/antiforgery/cachetiming-20050414.pdf

[<span id="ref-4">4</span>]: Meltdown: Reading Kernel Memory from User Space -
https://meltdownattack.com/meltdown.pdf

[<span id="ref-5">5</span>]: Spectre Attacks: Exploiting Speculative Execution -
https://spectreattack.com/spectre.pdf

[<span id="ref-6">6</span>]: Timing Attacks on Implementations of Diffie-Hellman, RSA, DSS, and Other
Systems - https://www.rambus.com/wp-content/uploads/2015/08/TimingAttacks.pdf

[<span id="ref-7">7</span>]: Differential Power Analysis -
https://paulkocher.com/doc/DifferentialPowerAnalysis.pdf

[<span id="ref-8">8</span>]: SoC it to EM: electromagnetic side-channel attacks on a complex
system-on-chip - https://www.iacr.org/archive/ches2015/92930599/92930599.pdf

[<span id="ref-9">9</span>]: Introduction To differential power analysis -
https://link.springer.com/content/pdf/10.1007/s13389-011-0006-y.pdf

[<span id="ref-10">10</span>]: Principles of Secure Processor Architecture Design -
https://caslab.csl.yale.edu/tutorials/hpca2019/ and
https://caslab.csl.yale.edu/tutorials/hpca2019/tutorial_principles_sec_arch_20190217.pdf

[<span id="ref-11">11</span>]: Time Protection - https://ts.data61.csiro.au/projects/TS/timeprotection/

[<span id="ref-12">12</span>]: Fault Attacks on Secure Embedded Software: Threats, Design and Evaluation -
https://arxiv.org/pdf/2003.10513.pdf

[<span id="ref-13">13</span>]: The Sorcerer's Apprentice Guide to Fault Attacks -
https://eprint.iacr.org/2004/100.pdf

[<span id="ref-14">14</span>]: Fault Mitigation Patterns -
https://www.riscure.com/uploads/2020/05/Riscure_Whitepaper_Fault_Mitigation_Patterns_final.pdf

[<span id="ref-15">15</span>]: SIFA: Exploiting Ineffective Fault Inductions on Symmetric Cryptography -
https://eprint.iacr.org/2018/071.pdf

<!-- Footnotes themselves at the bottom. -->

## Notes

[^1]: In other OpenTitan documents, the combination of technical and
    administrative defense are often referred to as "logical security"
