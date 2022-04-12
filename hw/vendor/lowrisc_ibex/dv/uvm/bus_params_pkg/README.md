# Bus parameters for DV utilities

The Ibex DV code uses a `dv_utils` support library vendored from
OpenTitan. This library needs some basic parameters: things like
bus address and data widths and similar.

The `dv_utils` library is supposed to be parametric, in that it should
work with any such widths, but a project that imports the library
needs to supply them in a SystemVerilog package called
`bus_params_pkg`. This directory contains that package, which can be
imported with the fusesoc core `lowrisc:ibex:bus_params_pkg`.
