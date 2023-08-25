# CSRNG HWIP Technical Specification

[`csrng`](https://reports.opentitan.org/hw/ip/csrng/dv/latest/report.html):
![](https://dashboards.lowrisc.org/badges/dv/csrng/test.svg)
![](https://dashboards.lowrisc.org/badges/dv/csrng/passing.svg)
![](https://dashboards.lowrisc.org/badges/dv/csrng/functional.svg)
![](https://dashboards.lowrisc.org/badges/dv/csrng/code.svg)

# Overview

This document specifies the Cryptographically Secure Random Number Generator (CSRNG) hardware IP functionality.
Due to the importance of secure random number generation (RNG), it is a topic which is extensively covered in security standards.
This IP targets compliance with both [BSI's AIS31 recommendations for Common Criteria (CC)](https://www.bsi.bund.de/SharedDocs/Downloads/DE/BSI/Zertifizierung/Interpretationen/AIS_31_Functionality_classes_for_random_number_generators_e.pdf), as well as [NIST's SP 800-90A](https://nvlpubs.nist.gov/nistpubs/SpecialPublications/NIST.SP.800-90Ar1.pdf) and [NIST's SP 800-90C (Second Draft)](https://csrc.nist.gov/CSRC/media/Publications/sp/800-90c/draft/documents/sp800_90c_second_draft.pdf), both of which are referenced in [FIPS 140-3](https://csrc.nist.gov/publications/detail/fips/140/3/final).
The CSRNG IP supports both of these standards for both deterministic (DRNG) and true random number generation (TRNG).
In NIST terms, it works with the [Entropy Source IP](../entropy_src/README.md) to satisfy the requirements as a deterministic random bit generator (DRBG) or non-deterministic random bit generator (NRBG).
In AIS31 language, this same implementation can be used to satisfy either the DRG.3 requirements for deterministic generation, or the PTG.3 requirements for cryptographically processed physical generation.

In this document the terms "DRNG" and "TRNG" are used most generally to refer to deterministic or true random number generation functionalities implemented to this specification.
However, the terms "DRBG" or "NRBG" are specifically used when respectively referring to SP 800-90A or SP 800-90C requirements.
Meanwhile, when addressing requirements which originate from AIS31 we refer to the specific DRG.3 or PTG.3 classes of RNGs.

This IP block is attached to the chip interconnect bus as a peripheral module conforming to the [comportability definition and specification](../../../doc/contributing/hw/comportability/README.md), but also has direct hardware links to other IPs for secure and software-inaccessible transmission of random numbers.
The bus connections to peripheral modules are done using the CSRNG application interface.
This interface allows peripherals to manage CSRNG instances, and request the CSRNG module to return obfuscated entropy.

## Features
- Provides support for both deterministic (DRNG) and true random number generation (TRNG), when combined with a secure entropy source (i.e. one constructed and implemented in compliance with SP 800-90A,B,C and AIS31).
  The TRNG mode is provided directly by the entropy source.
- Compliant with NIST and BSI recommendations for random number generation.
- Hardware peripherals and software applications issue commands to dedicated RNG instances through a common application interface.
- In deterministic mode, meets the requirements given in AIS31 for a DRG.3 class deterministic random number generator (DRNG) meaning it provides Forward Secrecy and Enhanced Backward Secrecy.
- Utilizes the CTR_DRBG construction specified in NIST SP 800-90A, qualifying it as a NIST-approved deterministic random bit generator (DRBG).
    - Operates at 256 bit security strength.
- Support for multiple separate CSRNG instances per IP block.
    - Each instance has its own internal state, control, reseed counters and IO pins.
    - The number of CSRNG instances is set via a module parameter.
- Software access to a dedicated CSRNG instance.
    - One instance, Instance N-1, is always accessible from the bus through device registers,
    - All other instances route to other hardware peripherals (e.g. the key manager, obfuscation engines, etc.) and in normal operation these other instances are inaccessible from software.
    - The IP may be configured to support "debug mode" wherein all instances can be accessed by software.
      For security reasons this mode may be permanently disabled using one-time programmable (OTP) memory.
- The IP interfaces with external entropy sources to obtain any required non-deterministic seed material (entropy) and nonces.
    - Requires an external entropy source which is compliant with NIST SP 800-90B, and which also satisfies the requirements for a PTG.2 class physical non-deterministic random number generator as defined in AIS31.
    - Dedicated hardware interface with external entropy source satisfies requirements for `get_entropy_input()` interface as defined in SP 800-90A.
    - This block does not use a derivation function and requires full entropy from the entropy source.
- Also supports the optional use of personalization strings or other application inputs (e.g. OTP memory values) during instantiation.
- Assuming a continuously-live entropy source, each instance can also optionally be used as a non-deterministic TRNG (true random number generator, also called a non-deterministic random bit generator or NRBG in SP 800-90C).
    - In this mode, an instance also meets the requirements laid out for a PTG.3 class RNG, the strongest class laid out in AIS31.
    - Implementation follows the NRBG "Oversampling Construction" approved by SP 800-90C, to meet both [Common Criteria (CC, ISO/IEC 15408)](https://www.iso.org/standard/50341.html) and FIPS TRNG constructions.
- In addition to the approved DRNG mode, any instance can also operate in "Fully Deterministic mode", meaning the seed depends entirely on application inputs or personalization strings.
    - This provides an approved means of seed construction in FIPS 140-2 as described in the [FIPS 140-2 Implementation Guidance](https://csrc.nist.gov/csrc/media/projects/cryptographic-module-validation-program/documents/fips140-2/fips1402ig.pdf), section 7.14, resolution point 2(a).

## Description

Though the recommendations in AIS31 are based around broad functional requirements, the recommendations in SP 800-90 are very prescriptive in nature, outlining the exact constructs needed for approval.
Thus the interface and implementation are largely driven by these explicit constructs, particularly the CTR_DRBG construct.

The CSRNG IP consists of four main components:
1. An AES primitive
2. The CTR_DRBG state-machine (`ctr_drbg_fsm`) which drives the AES primitive, performing the various encryption sequences prescribed for approved DRBGs in SP 800-90A.
These include:

    1. **The Derivation Function:**
       Part of the instantiation and reseed routines, this routine assembles the previous seed material (on reseed only), application inputs, and entropy.
    2. **The Instantiation Routine:**
       Combines application inputs, external entropy and nonce (more entropy) via the derivation function.
    3. **The Reseed Routine:**
       Combines the previous seed material with external entropy to generate a new seed.
    4. **The Generate Routine:**
       Generates up to CSRNG_MAX_GENERATE random bits.
       If called with prediction_resistance_flag, forces a reseed.
    5. **The Update Routine:**
       Updates the internal state of the DRNG instance after each generate call.
3. State vectors for each DRNG instance.
4. Interface logic and access control for each instance.

## Note on the term "Entropy"

Every DRNG requires some initial seed material, and the requirements for the generation of that seed material varies greatly between standards, and potentially between Common Criteria security targets.
In all standards considered, DRNGs require some "entropy" from an external source to create the initial seed.
However, the rules for obtaining said entropy differ.
Furthermore the required delivery mechanisms differ.
For this reason we must make a clear distinction between "Physical" (or "Live" or "True") entropy and "Factory Entropy".
This distinction is most important when considering the creation of IP which is both compatible with both the relatively new SP 800-90 recommendations, as well as the well-established FIPS 140-2 guidelines.

- Physical entropy is the only type of "entropy" described in SP 800-90.
The means of generation is described in [SP 800-90B](https://nvlpubs.nist.gov/nistpubs/SpecialPublications/NIST.SP.800-90B.pdf).
One statistical test requirement is that physical entropy must be unique between reboot cycles, ruling out sources such as one-time programmable (OTP) memories.
In SP 800-90A, the delivery mechanism must come through a dedicated interface and "not be provided by the consuming application".

- Factory entropy is a type of entropy described in the [FIPS 140-2 implementation guidance (IG)](https://csrc.nist.gov/csrc/media/projects/cryptographic-module-validation-program/documents/fips140-2/fips1402ig.pdf) section 7.14, resolution point 2(a).
It can be stored in a persistent memory, programmed at the factory.
In some use cases, the consuming application needs to explicitly load this entropy itself and process it to establish the expected seed.

This document aims to make the distinction between physical entropy and factory entropy wherever possible.
However, if used unqualified, the term "entropy" should be understood to refer to physical entropy strings which are obtained in accordance with SP 800-90C.
That is either physical entropy, or the output of a DRNG which itself has been seeded (and possibly reseeded) with physical entropy.
In AIS31 terms, "entropy strings" (when used in this document without a qualifier) should be understood to come from either a PTG.2 or PTG.3 class RNG.

### Security

All module assets and countermeasures performed by hardware are listed in the hjson countermeasures section.
Labels for each instance of asset and countermeasure are located throughout the RTL source code.

The bus integrity checking for genbits is different for software and hardware.
Only the application interface software port will have a hardware check on the genbits data bus.
This is done to make sure repeated values are not occurring.
Only 64 bits (out of 128 bits) are checked, since this is statistically significant, and more checking would cost more silicon.
The application interface hardware port will not have this check.
It is expected that the requesting block (EDN) will do an additional hardware check on the genbits data bus.

## Compatibility
This block is compatible with NIST's SP 800-90A and BSI's AIS31 recommendations for Common Criteria.
