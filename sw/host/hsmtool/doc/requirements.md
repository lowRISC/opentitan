# OpenTitan HSM Tooling

## Requirements

The OpenTitan tooling for HSM interactions should facilitate the generation and management of keys and the signing operations needed during the ceremony.
Managing the quorum and HSM configuration are typically proprietary operations that are not well serviced by the standard PKCS#11 interface.
These operations will be performed by the HSM vendor tools.

The tooling required to generate and manage keys and perform the signing operations should be developed by the OpenTitan software team.
This tooling (referred to as `hsmtool`) should be a small stand-alone program that can be built to run in the offline signing environment.

The software should have the following capabilities:

### Key Generation

`hsmtool` should support generating keys on the HSM with a number of different key profiles.
Examples include:
*   PROD keys should require authentication, should be sensitive and should not be extractable from the HSM.
*   DEV, TEST and RMA keys should require authentication, should be sensitive and should be extractable if they are wrapped.
*   Wrapping keys should require authentication, should be sensitive and should not be extractable from the HSM.

### Key Management

`hsmtool` should facilitate the import and export of keys in standard forms (such as PEM encoded PKCS#8).

TODO: understand and figure out how key wrapping and unwrapping works with import/export.

### Object Management

The PKCS#11 interface presents a generic object/attribute mechanism for managing objects known to the HSM.
`hsmtool` should provide interfaces for listing, modifying and destroying objects known to the HSM.

### Signing

`hsmtool` should support signing items (ie: SHA256 hashes) with HSM keys.
Signing should support any necessary transformations of the inputs and outputs required by the opentitan ROM (ie: the ROM works on PKCS#1 v1.5 signatures in little-endian order, but PKCS#11 requires entities to be in big-endian order).

## Implementation Principles

PKCS#11 objects are represented by a list of attributes and data (such as `CKA_KEY_TYPE: CKK_RSA` or `CKA_MODULUS_LEN: 3072`).
Requests to create new objects (such as keys) consist of a template of such values that are given to the HSM as part of the object creation request.
Considering that a list of key-value pairs is fundamental json data type, `hsmtool` will accept PKCS#11 attributes encoded as json maps.

To the extent possible, when importing and exporting keys, the standard PEM and DER encodings will be used.

Establishing a connection to an HSM (prior to issuing any requests) can be a time consuming operation.
The `hsmtool` CLI will also be representable as a list of json-encoded commands so that a sequence of HSM operations can be performed on a single connection.
