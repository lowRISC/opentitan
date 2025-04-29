# RFC: Move sigverify out of the mask ROM

Author: James Wainwright
Date: 2025-04-17
Status: draft

## Summary

This RFC proposes moving the silicon creator signature verification code from the mask ROM to the immutable ROM extension, which would no longer be optional nor signed.

The mutable ROM extension would be renamed to the FMC (first mutable code), and the term ROM extension would refer only to what we currently call the immutable ROM extension.

## Motivation

Moving sigverify out of the mask ROM enables:

* Fixing and updating the cryptography code post tape-out.
* Using different signature schemes for different SKUs of the same tape-out.

Signature verification is relatively complex code and removing it from the mask derisks tape-outs.

Allowing for personalised signature schemes increases the utility and value of a tape-out and potentially reduces costs if multiple customers can benefit. It also allows for SKUs which don't use signature verification and are closer to a generic microcontroller.

Experimental and new signature schemes (for example using post-quantum cryptography) can be tested on a subset of personalised silicon without needing to be included in all chips.

Simultaneously, making the immutable ROM extension non-optional simplifies the boot flow by keeping it linear.

## Explanation

The current boot process for Earlgrey at a high level is:

1. Mask ROM boots.
2. Signature verification of whole ROM extension.
3. (optional) Hash check of, then jump to, immutable ROM extension.
4. Jump to mutable ROM extension.
5. Signature verification of, then jump to, owner code.

The immutable ROM extension is currently a subset of the whole ROM extension and included in the silicon creator signature. Its hash is programmed to OTP during personalisation.

The proposed change to the boot process would be:

1. Mask ROM boots.
2. Hash check of, then jump to, immutable ROM extension.
3. Signature verification of, then jump to, mutable ROM extension.
4. Signature verification of, then jump to, owner code.

The responsibilities of the mask ROM are reduced to early silicon initialisation, RMA and bootstrap loops, and directly comparing the hash of the immutable ROM extension against the OTP value. Hash computation is simpler than signature verification and uses fixed-function hardware blocks.

The immutable ROM extension is now responsible for silicon creator signature verification and optionally DICE initialisation.

The mutable ROM extension's responsibilties are unchanged.

The immutable ROM extension would not be included in the signature for the mutable ROM extension, making them entirely separate stages. This distinction warrants a change of terminology to prevent confusing the two: the mutable ROM extension would be renamed to the FMC (first mutable code) while "ROM extension" would now refer only to the immutable ROM extension.

## Drawbacks

1. The mask ROM containing sigverify has already been taped-out and tested. Changing it would reduce the utility of existing test results.
2. Changing the name of the mutable ROM extension could cause confusion for existing project members.
3. Integrated flash is more expensive per-byte than mask ROM in terms of area/silicon cost.

## Rationale and alternatives

* We could continue to rely on heavy verification of sigverify to reduce tape-out risk. Moving sigverify would give us longer to fix any issues found by verification, however.
* We could not rename the immutable and mutable ROM extensions to prevent confusion. With the immutable ROM extension becoming required and more important, the need for terms like "imm_rom_ext" and "mut_rom_ext" would likely increase confusion instead.
* The immutable section could be programmed to OTP rather than flash if that has a cheaper silicon cost.

## Prior art

* FMC is the term used by DICE and Caliptra to describe the mutable signed stage after the mask ROM ([Caliptra - FMC Specification v1.0][fmc-spec]).

[fmc-spec]: https://github.com/chipsalliance/caliptra-sw/tree/main/fmc

## Unresolved questions

Does this move apply to integrated designs, and does it give the same utility?

## Future work

An implementation of the ROM extension that implements DICE alone without any signature verification, avoiding the need for key management.
