# Reset vs. Non-Reset Flops

## Overview

Various components inside OpenTitan operate on sensitive assets such as identities and key material.
This includes both the main processor core (executing cryptographic algorithms, configuring cryptographic hardware accelerators) and peripherals such as the key manager (key derivation, sideloading) and cryptographic accelerators themselves.
In most cases, such sensitive assets are locally registered in the hardware block and it is of high importance that they do not get exposed to potential adversaries even with physical access to the chip.
This is especially true for devices in the PROD life-cycle state, i.e., when the device has potentially access to device root secrets.

This document describes
i) different flip-flop types for registering such sensitive assets inside OpenTitan hardware blocks incl. possible vulnerabilities,
ii) the interplay with other countermeasures and security hardening schemes, and
iii) why we **do not give a general recommendation for either flip-flop type** for sensitive assets in the earlier hardware design stages of OpenTitan IP.

Instead, it is **recommended** to take this decision later in the design process on a sub-block level in consideration of all countermeasures and security hardening employed.

A specific example where it has been decided to use non-reset flops in OpenTitan is discussed in the [appendix](#appendix-otbn---a-case-for-non-reset-flops).

## Flip-Flop Types

At register-transfer level (RTL), OpenTitan considers two different flip-flop (flop) types for implementing registers: Reset Flops[^1] and Non-Reset Flops.
The main difference between the two is the behavior upon reset: The former puts the storage element into a well-defined state, whereas in the latter the value inside the storage element is not altered.
From a security perspective, both behaviors need consideration.

### Reset flops

Putting the storage element into a well-defined state upon reset automatically wipes any content from the storage element, but directly exposes the Hamming distance between the content (a potential secret) and the reset value in side-channel analysis (SCA).

This means that after a reset, there is no need to worry about sensitive data from before the reset being somehow extracted.
This helps to keep the design simple.
However, the possibility of exposing the Hamming distance between secret and reset can make such flops an attractive target for (localized) reset glitch attacks.

The practicability of and susceptibility to such attacks depends on various factors.
The following points should be considered.

- To directly extract sensitive assets using a localized reset glitch attack, a combined attack using fault injection (FI) with high precision (needs to be highly localized) and differential power analysis (DPA) is needed.
  This may be hard to achieve.
- Instead of trying to directly extract sensitive assets, adversaries are often interested in breaking down the problem into smaller parts with much smaller hypothesis space, e.g. to the byte level as in a single AES S-Box, and where there is the possibility to explore, e.g., by getting different views over time (the behavior of a single hardware S-Box may depend on previous observations but still gives additional information), and not just doing the same experiment over and over again.
  As opposed to that, a register bank inside a peripheral holding e.g. a full key of say 256 bits, or even a sub part of 32/64 bits is harder to attack as i) the same sub part of the key will always be in the same sub register, ii) the hypothesis space is considerably larger, and iii) there is no variation between subsequent repetitions of the same localized glitch attack.
- For the same reasons, the weak spot is often not the transition of the sensitive asset (e.g. over a bus into a peripheral register) but the usage of it, i.e., the heavy and predictable processing using the sensitive asset inside peripherals such as AES.
  To protect such critical cores, designers resort to different countermeasures for security hardening and this suggests that the susceptibility to reset glitch attacks should be viewed in the context of these measures (see below).
- Sidenote: Relying on glitch detectors for detecting localized glitches and initiating a complete system reset or alternatively a wipe with random data on top of the asynchronous reset is probably not sufficient as even a minimal delay of a couple of cycles between the glitch and the wipe can suffice to capture the Hamming distance.
  In OpenTitan, already the alert handler triggering the system reset has a delay of multiple cycles.

### Non-reset flops

Not altering the value inside the storage element upon a reset has the advantage of completely avoiding the Hamming distance leakage during reset which makes the design much more robust against reset glitch attacks.

However, leaving the value of the storage element untouched upon a reset requires special care to avoid that sensitive assets get into the wrong hands after a reset.
First of all, architectural support is needed to clear all such flops with random data during reboot.
This can be done either completely in hardware (a peripheral that clears itself automatically after reset release), in hardware but triggered by software, or completely in software (like reset-less register files in processor cores without special security focus).
Only after successful clearing, the corresponding module shall become operational (this also holds for entering scan mode).

But even with such functionality implemented, new and maybe lesser known attack windows may open up that can be hard to protect against or require additional, sometimes exotic countermeasures at system level and thorough security review.
To give some examples:
- Fault injection (FI) attacks on the clearing infrastructure could be leveraged to bypass the clearing.
  Shadow registers would have to be used to mitigate this.
- VCMAIN-GND capacitance measurements with the device held in reset: The measured capacitance solely depends on the Hamming weight of the sensitive value (in the non-reset flops) plus a constant.
  To prevent this, a large number of non-reset flops would have to be pre-charged with random data to add noise as the power supply goes down or as the reset is detected.
  While theoretically possible under some assumptions, this involves complications.

Therefore, it cannot be generally recommended to use non-reset flops instead of reset flops just to avoid targeted reset glitch attacks.
Non-reset flops should only be used if there is well defined concern and in consideration of all other countermeasures and security hardening employed.

## Scan Mode

Theoretically, scan mode could be misused to simply scan sensitive assets out of registers.
The obvious approach of taking all registers potentially holding sensitive data off the scan chain is not a viable solution.
This may affect many registers (e.g. ~1400 flops for unhardened AES) and have a very big impact on design for testability (DFT).

In OpenTitan, the device is only allowed to enter scan mode in the TEST and RMA life-cycle states, in which no device root secrets are in the device yet or any more, respectively. Consequently, what really needs to be protected is i) the life-cycle transition from PROD to RMA where the critical hardware secrets are “erased/overwritten” (this transition should itself force a device reset), ii) scan mode entry while the device is in PROD state, and iii) scan mode exit while the device is in PROD state (to prevent the use of scan mode for arbitrary data injection).
This protection is needed irrespective of the selected flop type and whether registers potentially holding sensitive assets have been disconnected from the scan chain.
This means that in OpenTitan, there is no benefit in taking such registers off the scan chain.
Scan mode needs to be protected anyway.

Scan FFs vs. SCA: Scan chain insertion through synthesis will connect FFs to one another without regarding whether they are e.g. handling either share of a masked implementation. In this way, scan outputs (which equals Q) are connected to input multiplexers of SI and D within FFs.
This could traverse share boundaries of masked implementations.
The assumption is though, that the scan enable SE is glitch free and only active as described above so that signals will not actually recombine and lead to unforeseen unmasking, hence, reduction of masking order.

## Interplay with other Countermeasures and Security Hardening

In many cases, the weak spot of sensitive assets is not their storage in a peripheral register and transition from one block into another (e.g. over a bus), but the usage of the asset such as in heavy, predictable data processing potentially happening on just a subset of the asset with a small-sized hypothesis space (e.g. a single byte-sized S-Box in AES).
Such functionality is typically protected against SCA by additional countermeasures implemented later during the design process in a security hardening phase.
Obviously the implemented countermeasures have a big impact on the susceptibility to various attack types and therefore must be known when weighing up the risks of non-reset vs. reset flops for the considered OpenTitan hardware block.

For illustration, consider the following two examples.

1. A particular hardening scheme periodically writes a critical register with random data before and after writing the actual sensitive asset (or parts of it) to randomize the Hamming distance leakage[^2].
   This register should likely use non-reset flops as a repeated, localized reset glitch attack can substantially weaken the hardening scheme.
2. A masking scheme that processes and stores the sensitive asset in multiple shares[^3].
   Since the Hamming weights of the two shares are not proportional to the Hamming weight of the sensitive asset, there is no point in protecting the registers holding the shares against reset glitch attacks.

## Conclusion

This document discusses non-reset and reset flops for registering sensitive assets and outlines possible vulnerabilities.
It has further been outlined that the susceptibility to such attacks highly depends on other block-specific countermeasures for security hardening.
For this reason, **we do not give a general recommendation for either flip-flop type** for sensitive assets in the earlier hardware design stages of OpenTitan hardware blocks.
Instead, it is **recommended** to take this decision later in the design process on a sub-block level in consideration of all countermeasures and security hardening employed.

## Appendix: OTBN - a Case for Non-Reset Flops

The [OpenTitan Bignum accelerator (OTBN)](../../../../hw/ip/otbn/README.md) is a coprocessor for asymmetric cryptographic operations like RSA or elliptic curve cryptography (ECC).
To harden the execution of such operations against SCA and FI, a variety of software and hardware countermeasures are used.
Software typically pre-charges registers with pseudo-random data before writing (masked) secrets to avoid SCA leakage.
Also, software (re-)masks sensitive intermediate results in the register files with pseudo-random data taken either from one of the random number generator interfaces or other registers.
A reset glitch attack on the involved registers might thus help to weaken these countermeasures.
In addition, FI attacks including reset glitch attacks may aim at partially zeroing registers, e.g., to zero parts of a scalar in ECC-based signature schemes, thereby substantially weakening the signature scheme and enabling cryptographic attacks on the outputs of the operation.

At the same time, OTBN implements a secure wipe mechanism to ensure that no register and memory contents survive a chip reset.
Moreover, several hardware countermeasures are in place to allow entering scan mode only in the TEST and RMA life-cycle states of OpenTitan, in which no device root secrets are in the device yet or any more, respectively.

For these reasons, it has been decided to switch to non-reset flops for the general and wide data register files in OTBN when approaching the D2S milestone.

<!-- Footnotes themselves at the bottom. -->

## Notes

[^1]: Inside OpenTitan hardware blocks, all reset flops use an asynchronous, active-low reset with synchronous release.

[^2]: This is typically done when employing masking in software, e.g., inside the OpenTItan Bignum accelerator.

[^3]: In a nutshell, when using two shares this means to create a second copy of the circuit.
      At the beginning of the operation, a random value is drawn.
      The second circuit then processes this random value (the mask), whereas the original circuit processes the masked input, i.e., the sum (XOR) of the original input (our sensitive asset) and the mask.
      Eventually, the output mask (Circuit 2) is subtracted (XORed) from the masked output (Circuit 1) to get the actual output.
