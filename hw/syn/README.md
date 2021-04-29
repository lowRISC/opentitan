# OpenTitan Synthesis Flow

This readme gives some quick instructions on how to run synthesis in OpenTitan, using top_earlgrey as an example.

## Normal Synthesis Through dvsim

To run synthesis through dvsim, use a command like the following:

```
$ cd $REPO_TOP
$ ./util/dvsim/dvsim.py -t dc hw/top_earlgrey/syn/chip_earlgrey_asic_syn_cfg.hjson --purge --local
```

This comment will invoke dvsim to run synthesis and terminate upon success or failure.
The synthesis results are placed in the scratch area under `$SCRATCH_ROOT/{branch_name}/chip_earlgrey_asic-syn-dc/` for this example command.

The main script that powers synthesis is `hw/syn/tools/dc/run-syn.tcl`.

To follow the progress of the different synthesis flow stages (analysis, elaboration, etc.), it is recommended to use the `tail -f` command on the report file of interest.

For example, overall status can be observed with
```
tail -f `$SCRATCH_ROOT/{branch_name}/chip_earlgrey_asic-syn-dc/default/synthesis.log`
```

Another example would be the elaboration status
```
tail -f `$SCRATCH_ROOT/{branch_name}/chip_earlgrey_asic-syn-dc/default/REPORTS/elab.rpt`
```

## Re-run Interactive Synthesis

Assuming the above synthesis steps produces an error or creates a situation where we must run synthesis interactively for debug, it can be done as follows.

When the normal synthesis steps are run (see example above), an output file called `env_variables.tcl` is created in the synthesis scratch area, `$SCRATCH_ROOT/{branch_name}/chip_earlgrey_asic-syn-dc/default` in the above example.

To re-run this synthesis interactively, do the following:

```
$ cd $SCRATCH_ROOT/{branch_name}/chip_earlgrey_asic-syn-dc/default/syn-icarus
$ dc_shell

```

The above command opens dc_shell in the scratch area.
Once dc_shell is open, do the following:

```
$ source ../env_variables.tcl
$ source $REPO_TOP/hw/syn/tools/dc/run-syn.tcl

```

Now, synthesis will begin again but will not exit dc_shell upon completion.
If you do not wish for synthesis to run that far, `run_syn.tcl` can be directly modified to add or skip steps.


## Loading DDC After Synth Completion
If a synthesis job has completed and you would like to reload the session for more details, follow the steps below

```
$ cd $SCRATCH_ROOT/{branch_name}/chip_earlgrey_asic-syn-dc/default/syn-icarus
$ dc_shell

```

The above command opens dc_shell in the scratch area.
Once dc_shell is open, do the following:

```
$ source ../env_variables.tcl
$ set foundry_root "$::env(foundry_root)"
$ source "${foundry_root}/syn/dc/setup.tcl"
$ read_ddc DDC/mapped.ddc

```

This will begin reading in the libraries and load up the database for further analysis / experiments.
