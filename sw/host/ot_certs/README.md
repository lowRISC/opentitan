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

The asn1 template supports five variable types: byte-array, string, integer,
boolean, and selector.

Array types (byte-array, string, and integer) require the size in bytes of the
value it represents to be specified.

```javascript
type: "integer", // or "string" or "byte-array"
exact-size: 20, // or `range-size: [min, max]` if size could be variable
```

The selector type is a special integer type (always 32-bit) used to select a
branch in a dynamic choice. It requires `num_choices` to be specified.

```javascript
type: "selector",
num_choices: 3,
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

### Algorithm Variants

The template engine supports dynamic branching between alternative algorithms
(e.g., between ML-DSA and ECDSA) using `choices`. This allows a single template
and device builder function to generate hybrid certificate endorsements based
on a runtime parameter.

The selection is controlled by a `selector` variable, which must be of type
`selector`. The length of the `choices` array must match the `num_choices`
declared in the selector variable.

```javascript
subject_public_key_info: {
    selector: "pub_key_type", // A selector variable defined in `variables`
    choices: [
        {
            algorithm: "ec-public-key",
            curve: "prime256v1",
            public_key: {
                x: { var: "pub_key_ec_x" },
                y: { var: "pub_key_ec_y" },
            }
        },
        {
            algorithm: "mldsa-65",
            public_key: { var: "pub_key_mldsa_65" },
        },
        {
            algorithm: "mldsa-87",
            public_key: { var: "pub_key_mldsa_87" },
        }
    ]
}
```

When generating C code, the engine places precomputed DER constants for all
branches into Flash (`.rodata`) and automatically emits an `if/else` block
with pointer skip adjustments (`template_skip_const`).
