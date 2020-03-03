# RTL Linting

Linting is a productivity tool for designers to quickly find typos and
bugs at the time when the RTL is written. Running lint is important
when using SystemVerilog, a weakly-typed language, unlike other hardware
description languages. We consider linting to be critical for conformance
to our goals of high quality designs.

Currently, due to the proprietary nature of tool collateral, all linting
activity is done offline and reported back to designers.  The project will
standardize on a particular linting tool, and results will be shared in
some form through continuous integration build results, published tool
outputs, pre-submit checks, and/or linting summaries of tool output
(TODO: publication details).  At that time this README will be updated
with setup and run instructions.

# CDC Linting

Logic designs that have signals that cross from one clock domain to
another unrelated clock domain are notorious for introducing hard to
debug problems.  The reason is that design verification, with its constant
and idealized timing relationships on signals, does not represent the
variability and uncertainty of real world systems.  For this reason,
maintaining a robust Clock Domain Crossing verification strategy ("CDC
methodology") is critical to the success of any multi-clock design.

Currently, due to the proprietary nature of tool collateral, all CDC linting
activity is done offline and reported back to designers.  The project will
standardize on a particular CDC linting tool, and results will be shared in
some form through continuous integration build results, published tool
outputs, pre-submit checks, and/or linting summaries of tool output
(TODO: publication details).  At that time this README will be updated
with setup and run instructions.

This holds for *Reset Domain Crossing* ("RDC") methodology as well.
