# Clock Manager HWIP Technical Specification
<!-- BEGIN CMDGEN util/mdbook_regression_links.py --hjson hw/top_${topname}/ip_autogen/clkmgr/data/clkmgr.hjson --top ${topname} -->
<!-- END CMDGEN -->

**NOTE**: This document describes the planned split of the clock manager into an always-on (AON) part and a power-gated (Main) part, including the software re-initialisation requirement.
The split is not implemented in the RTL yet; until it is, the clock manager resides entirely in the AON power domain and its state is retained during deep sleep.

# Overview

This document specifies the functionality of the OpenTitan clock manager.

${"##"} Features

- Attribute based controls of OpenTitan clocks.
- Minimal software clock controls to reduce risks in clock manipulation.
- External clock switch support.
- Clock frequency/time-out measurement.
- Split into an always-on (AON) part and a power-gated (Main) part, to reduce power consumption during deep sleep:
  - The Main part contains all high-frequency logic: clock division, root/software/transactional gating, frequency measurement, and the CSRs.
  - The AON part only buffers the AON clock.
  - The CSRs lose their values during deep sleep. Software must re-initialise the configuration CSRs after returning from deep sleep.
