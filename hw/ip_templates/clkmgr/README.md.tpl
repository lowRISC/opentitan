# Clock Manager HWIP Technical Specification
<!-- BEGIN CMDGEN util/mdbook_regression_links.py --hjson hw/top_${topname}/ip_autogen/clkmgr/data/clkmgr.hjson --top ${topname} -->
<!-- END CMDGEN -->

# Overview

This document specifies the functionality of the OpenTitan clock manager.

${"##"} Features

- Attribute based controls of OpenTitan clocks.
- Minimal software clock controls to reduce risks in clock manipulation.
- External clock switch support.
- Clock frequency /time-out measurement.
- To reduce power consumption during deep sleep this IP supports:
  - A split architecture to allow separation of AON from power-gated logic.
  - All high frequency logic resides in the power-gated domain, including clock measurement.
  - The CSRs are placed in the power-gated domain and therefore require mandatory re-initialisation after deep sleep.
  - This leaves minimal logic for the AON domain.
