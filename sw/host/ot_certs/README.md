# OpenTitan certificate generator

*[Click here for the generated documentation of `ot_certs`.](https://opentitan.org/gen/rustdoc/ot_certs)*

This crate is capable of generating OpenTitan certificates to be stored on the
device.

Certificates templates are specified in Hjson format. Fields of the certificate
can be given literal values in the template, or given the name of a variable.
These variable values are intended to be set by the OpenTitan device itself.
This crate will generate code capable of running on the device to get/set these
fields.

More detailed documentation on OpenTitan certificates will be published soon.


### ASN1 Variable Typing

The asn1 template supports four variable types: byte-array, string, integer, and
boolean. Array types (byte-array, string, and integer) require the size in bytes
of the value it represents to be specified.

```javascript
type: "integer", // or "string" or "byte-array"
exact-size: 20, // or `range-size: [min, max]` if size could be variable
```

When the variable is an integer, the size is determined using its big-endian
array representation without any additional zero prefixes.

The byte-array can also be encoded as an integer. This requires the `tweak-msb`
field to be set, and the builder will always set the MSb when encoding as an
integer to ensure a fixed size encoding. If MSb tweak is not possible, please
consider typing it as an integer instead.

```javascript
type: "byte-array",
exact-size: 20, // or `range-size: [min, max]` if size could be variable
[tweak-msb: true,] // if destination could be an integer
```
