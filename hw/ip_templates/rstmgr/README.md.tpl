# Reset Manager HWIP Technical Specification
<!-- BEGIN CMDGEN util/mdbook_regression_links.py --hjson hw/top_${topname}/ip_autogen/rstmgr/data/rstmgr.hjson --top ${topname} -->
<!-- END CMDGEN -->

# Overview

This document describes the functionality of the reset controller and its interaction with the rest of the OpenTitan system.

${"##"} Features

*   Stretch incoming POR.
*   Cascaded system resets.
*   Peripheral system reset requests.
*   RISC-V non-debug-module reset support.
*   Limited and selective software controlled module reset.
*   Always-on reset information register.
*   Always-on alert crash dump register.
*   Always-on CPU crash dump register.
*   Reset consistency checks.
