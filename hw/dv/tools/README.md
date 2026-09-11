# Tools

## Debugging with the simulator GUI

`dvsim` runs a simulation in the GUI with `--gui`, and with `--gui-debug` (`-gd`) it also enables the tool debug features: breakpoints, live values and transaction recording.
Both are limited to a single cfg and a single test.
`--gui-debug` is available for Xcelium only.

With Xcelium, a GUI run compiles and elaborates from the run step instead of loading the snapshot that the build step produced.
The session is therefore a single-step `xrun` invocation, which means "Reinvoke Simulator..." in SimVision recompiles whatever changed and reloads the design in place.
An RTL or DV fix can be picked up without leaving the GUI, so the waveform, the probes and the breakpoints survive the edit.
The run step is not a second full build: xrun checks the library the build step populated and, with nothing changed, compiles and elaborates nothing before handing control to SimVision.

Three things are worth knowing before using it:

- Xcelium compiles the sources where they live, rather than the copies that FuseSoC exports into the build tree, since SimVision would otherwise recompile the copies and never see the edit.
This applies to batch builds as well, so that batch and GUI key their object libraries to the same paths and share one build directory.
The trade is that an edit landing while the build step is running is picked up, where the other tools build from a snapshot taken at the start.
Every Xcelium `-I` names the source tree for the same reason; a new DPI core needs its include path written that way, not as a path under `fusesoc-work/src`.

- The run step has to compile with the same options as the build step, or it would simulate a differently configured design, since individual cfgs and build modes add their own defines, include paths and DPI libraries.
dvsim therefore records the options of every build in `build_opts.f` in the build directory, and a GUI run reads them back.
Nothing needs to be repeated by hand in the hjson, and there is one place to look when the two do appear to disagree.
Because the file is written for every build, `--gui --run-only` can attach to a build made without `--gui`, which is the quickest way into a failing regression test.
That build carries none of the debug options the `gui` and `gui_debug` build modes add, so a session that needs breakpoints or live values needs a `--gui` build of its own.

- Two sessions on the same cfg and build mode share an object library, and xrun serialises them: the second waits on `.xmlib.lock` with `*W,WKWTLK` until the first exits.
Give each its own scratch tree with `-br <name>` to run them side by side.
If the run being debugged was built with `--build-seed`, pass the same value again when building for the GUI, since dvsim does not carry the seed over on its own.
