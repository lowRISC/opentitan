# bus_params_pkg

This package provides an isolation for all common verification components under
`hw/dv/sv/` from the OpenTitan specific design constants provided in
`hw/top_earlgrey/rtl/top_pkg.sv`. This mostly includes common bus parameters
such as address and data widths.

When vendoring the common DV code into another repo, the other repo must
provide its own implementation of `bus_params_pkg` so that the
dependency on the `top_pkg` can be avoided.
