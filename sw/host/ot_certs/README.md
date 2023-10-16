# OpenTitan certificate generator

This crate is capable of generating OpenTitan certificates to be stored on the
device.

Certificates templates are specified in Hjson format. Fields of the certificate
can be given literal values in the template, or given the name of a variable.
These variable values are intended to be set by the OpenTitan device itself.
This crate will generate code capable of running on the device to get/set these
fields.

More detailed documentation on OpenTitan certificates will be published soon.
