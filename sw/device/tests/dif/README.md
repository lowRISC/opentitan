# The OpenTitan DIFs (Device Interface Functions) Library unit tests

The purpose of DIF unit tests is to verify that the operations performed by the
API match the expectations.

For a detailed information on DIFs, please refer to the "DIF Style Guide"
`sw/device/lib/dif/README.md`.

## Testing strategy

Peripherals are designed to perform a set of specific operations, so it is not
possible to define a complete list of tests that would uniformly cover all the
different DIF libraries. However, there are many commonalities that DIF APIs
exhibit, which in turn makes it possible to define a set of minimal required
tests.

### Function error codes

* When defined, DIF API must be able to return every variant of the error code
  associated with this API.

### Common register access patterns

* Enable/disable/set/unset/... API often perform a simple set of operations that
  simply access a register bit or field at given offset. In this case an access
  to the first and last element of the register must be tested. If the elements
  are split across multiple same function registers (multi reg), the access to
  the first and last element of the first and last register must be tested.
