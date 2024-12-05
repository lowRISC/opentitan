# Registers

The flash protocol controller maintains two separate access windows for the FIFO.
It is implemented this way because the access window supports transaction back-pressure should the FIFO become full (in case of write) or empty (in case of read).

<!-- BEGIN CMDGEN util/regtool.py -d ./hw/top_${topname}/ip_autogen/flash_ctrl/data/flash_ctrl.hjson -->
<!-- END CMDGEN -->
