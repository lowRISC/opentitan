# RFC: Move sigverify out of the mask ROM

Author: James Wainwright
Date: 2025-04-17
Status: draft

## Summary

This RFC proposes moving the silicon creator signature verification code from the mask ROM to the immutable section, which would no longer be optional nor signed.

## Motivation

Moving sigverify out of the mask ROM enables:

* Fixing and updating the cryptography code post tape-out.
* Using different signature schemes for different SKUs of the same tape-out.

Signature verification is relatively complex code and removing it from the mask derisks tape-outs.

Allowing for personalised signature schemes increases the utility and value of a tape-out and potentially reduces costs if multiple customers can benefit. It also allows for SKUs which don't use signature verification and are closer to a generic microcontroller.

Experimental and new signature schemes (for example using post-quantum cryptography) can be tested on a subset of personalised silicon without needing to be included in all chips.

Simultaneously, making the immutable section non-optional simplifies the boot flow by keeping it linear.

## Explanation

The current boot process for Earlgrey at a high level is:

1. Mask ROM boots.
2. Signature verification of whole ROM extension.
3. (optional) Hash check of, then jump to, immutable section.
4. Jump to ROM extension.
5. Signature verification of, then jump to, owner code.

The immutable section is currently a subset of the whole ROM extension and included in the silicon creator signature. Its hash is programmed to OTP during personalisation.

The proposed change to the boot process would be:

1. Mask ROM boots.
2. Hash check of, then jump to, immutable section.
3. Signature verification of, then jump to, ROM extension.
4. Signature verification of, then jump to, owner code.

The responsibilities of the mask ROM are reduced to early silicon initialisation, RMA and bootstrap loops, and directly comparing the hash of the immutable section against the OTP value. Hash computation is simpler than signature verification and uses fixed-function hardware blocks.

The immutable section is now responsible for silicon creator signature verification and optionally DICE initialisation.

The ROM extension's responsibilties are unchanged.

The immutable section would not be included in the signature for the ROM extension, making them independent stages in separate portions of flash.

## Drawbacks

1. The mask ROM containing sigverify has already been taped-out and tested. Changing it would reduce the utility of existing test results.
2. Integrated flash is more expensive per-byte than mask ROM in terms of area/silicon cost.
   * The size of sigverify is approximately 10KiB as of Earlgrey 1.0.0.

## Rationale and alternatives

* We could continue to rely on heavy verification of sigverify to reduce tape-out risk. Moving sigverify would give us longer to fix any issues found by verification, however.
* The immutable section could be programmed to OTP rather than flash if that has a cheaper silicon cost.

## Unresolved questions

Does this move apply to integrated designs, and does it give the same utility?

## Future work

An implementation of the ROM extension that implements DICE alone without any signature verification, avoiding the need for key management.
