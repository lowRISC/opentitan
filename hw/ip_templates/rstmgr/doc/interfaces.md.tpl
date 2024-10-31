# Hardware Interfaces

## Parameters

The following table lists the instantiation parameters of `rstmgr`.

Parameter                   | Default       | Description
----------------------------|---------------|---------------
`SecCheck`                  | 1             | Enables reset consistency checks on the leaf reset.  Each check contains a small FSM.
`SecMaxSyncDelay`           | 2             | The default synchronization delay assumptions used in reset consistency checks.  If a design uses a sync cell with more stages of delay, that value should be supplied.


## Signals

<!-- BEGIN CMDGEN util/regtool.py --interfaces ./hw/top_${topname}/ip_autogen/rstmgr/data/rstmgr.hjson -->
<!-- END CMDGEN -->
